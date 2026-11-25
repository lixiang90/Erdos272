module

public import Erdos272.Counting.N86412.APBalanced86412

@[expose] public section

namespace JSP233.APTemplateArithmetic86412
open APBalanced86412
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem quotient_frame {n q : ℕ} (hq : 3≤q) (hn : q<n) :
    1≤n/q ∧ n/q+1≤n-1 ∧ 3≤n-n/q ∧
      1≤n-n/q-(n/q+1) ∧ n-n/q≤n-1 := by
  let D := n/q
  have hq0 : 0<q := by omega
  have hD : 1≤D := Nat.div_pos (by omega) hq0
  have hrem : n%q+q*D=n := Nat.mod_add_div n q
  have hprod : 3*D≤q*D := Nat.mul_le_mul_right D hq
  have hzero : n%q=0 → 2≤D := by
    intro hz
    by_contra hh
    have hD1 : D=1 := by omega
    rw [hD1, Nat.mul_one, hz, Nat.zero_add] at hrem
    omega
  by_cases hz : n%q=0
  · have hD2 := hzero hz
    change 1≤D ∧ D+1≤n-1 ∧ 3≤n-D ∧ 1≤n-D-(D+1) ∧ n-D≤n-1
    omega
  · change 1≤D ∧ D+1≤n-1 ∧ 3≤n-D ∧ 1≤n-D-(D+1) ∧ n-D≤n-1
    omega

theorem nested_balanced_tail {n q : ℕ} (hq : 3≤q) (hn : q<n) (hr : n%q≠0) :
    BalancedTail (n-n/q) (q-1) (n/q+1) := by
  let D := n/q
  let r := n%q
  let t := n-D
  have hq0 : 0<q := by omega
  have hqm0 : 0<q-1 := by omega
  have hrem : r+q*D=n := Nat.mod_add_div n q
  have hr0 : 0<r := by dsimp only [r]; omega
  have hrq : r<q := Nat.mod_lt n hq0
  have hprod : (q-1)*D+D=q*D := by
    have he : q-1+1=q := by omega
    have hh := congrArg (fun z : ℕ => z*D) he
    simpa only [Nat.add_mul, one_mul] using hh
  have ht : t=(q-1)*D+r := by dsimp only [t]; omega
  have hm1 : (D+1)*(q-1)=(q-1)*D+(q-1) := by ring
  unfold BalancedTail
  change D+1=t/(q-1) ∨ (t%(q-1)≠0 ∧ D+1=t/(q-1)+1)
  by_cases hre : r=q-1
  · have hte : t=(D+1)*(q-1) := by omega
    have hm2 : (D+1+1)*(q-1)=(D+1)*(q-1)+(q-1) := by ring
    have hd : t/(q-1)=D+1 := Nat.div_eq_of_lt_le (by omega) (by omega)
    exact Or.inl hd.symm
  · have hrl : r<q-1 := by omega
    have hd : t/(q-1)=D := Nat.div_eq_of_lt_le
      (by simpa only [Nat.mul_comm D (q-1)] using (by omega : (q-1)*D≤t))
      (by omega)
    have hm := Nat.mod_add_div t (q-1)
    rw [hd] at hm
    have hmr : t%(q-1)=r := by omega
    exact Or.inr ⟨by rw [hmr]; omega, by rw [hd]⟩

#print axioms quotient_frame
#print axioms nested_balanced_tail
end JSP233.APTemplateArithmetic86412
