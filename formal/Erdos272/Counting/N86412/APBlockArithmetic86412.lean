module

public import Erdos272.Counting.N86412.APBalanced86412

@[expose] public section

namespace JSP233.APBlockArithmetic86412
open APBalanced86412
set_option autoImplicit false
set_option maxHeartbeats 1000000

def Left3 (n : ℕ) : ℕ := n/3+if n%3=2 then 1 else 0
def Middle3 (n : ℕ) : ℕ := n/3+if n%3=0 then 0 else 1
def Right3 (n : ℕ) : ℕ := n/3

def EndLeft (n q : ℕ) : ℕ := n/q+if n%q=q-1 then 1 else 0
def EndRight (n q : ℕ) : ℕ := n/q

theorem balanced_two_parts {a b : ℕ} (ha : a≤b+1) (hb : b≤a+1) :
    BalancedTail (a+b) 2 a ∧ BalancedTail (a+b) 2 b := by
  unfold BalancedTail
  omega

theorem three_blocks {n : ℕ} (hn : 4≤n) :
    Left3 n+Middle3 n+Right3 n=n ∧ 2≤Middle3 n ∧
      1≤Left3 n ∧ 1≤Right3 n ∧
      Middle3 n-1≤Left3 n ∧ Left3 n≤Middle3 n ∧
      Middle3 n-1≤Right3 n ∧ Right3 n≤Middle3 n ∧
      BalancedTail n 3 (Left3 n) ∧ BalancedTail n 3 (Right3 n) := by
  unfold Left3 Middle3 Right3 BalancedTail
  split_ifs <;> omega

theorem recursive_end_cuts {n q : ℕ} (hq : 4≤q) (hn : q+1≤n) :
    1≤EndLeft n q ∧ 1≤EndRight n q ∧
      BalancedTail n q (EndLeft n q) ∧ BalancedTail n q (EndRight n q) ∧
      q≤n-EndLeft n q ∧ q≤n-EndRight n q ∧
      3≤n-EndLeft n q-EndRight n q := by
  let D := n/q
  have hq0 : 0<q := by omega
  have hrem : q*D+n%q=n := by
    dsimp only [D]
    have hh := Nat.mod_add_div n q
    omega
  have hrq : n%q<q := Nat.mod_lt n hq0
  have hD : 1≤D := by
    exact Nat.div_pos (by omega) hq0
  have hq1 : q-1+1=q := Nat.sub_add_cancel (by omega : 1≤q)
  have hq2 : q-2+2=q := Nat.sub_add_cancel (by omega : 2≤q)
  have hprod1 : (q-1)*D+D=q*D := by
    have hh := congrArg (fun z : ℕ => z*D) hq1
    simpa only [Nat.add_mul, one_mul] using hh
  have hprod2 : (q-2)*D+2*D=q*D := by
    have hh := congrArg (fun z : ℕ => z*D) hq2
    simpa only [Nat.add_mul] using hh
  have hbound1 : (q-1)*1≤(q-1)*D := Nat.mul_le_mul_left (q-1) hD
  have hbound2 : (q-2)*1≤(q-2)*D := Nat.mul_le_mul_left (q-2) hD
  have hbound4 : 4*D≤q*D := Nat.mul_le_mul_right D hq
  have hzeroD : n%q=0 → 2≤D := by
    intro hz
    by_contra hh
    have hone : D=1 := by omega
    rw [hone, Nat.mul_one, hz, Nat.add_zero] at hrem
    omega
  unfold EndLeft EndRight BalancedTail
  split_ifs with he
  · omega
  · by_cases hz : n%q=0
    · have hd2 := hzeroD hz
      have hbound : (q-1)*2≤(q-1)*D := Nat.mul_le_mul_left (q-1) hd2
      omega
    · omega

#print axioms balanced_two_parts
#print axioms three_blocks
#print axioms recursive_end_cuts
end JSP233.APBlockArithmetic86412
