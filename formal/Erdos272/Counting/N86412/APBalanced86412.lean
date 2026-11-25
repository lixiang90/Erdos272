module

public import Erdos272.Arithmetic.APInterval208

@[expose] public section

namespace JSP233.APBalanced86412
open ActualAPCount208 APInterval208 PureSource208
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def BalancedTail (n q b : ℕ) : Prop :=
  b=n/q ∨ (n%q≠0 ∧ b=n/q+1)

theorem floor_split_cost {q : ℕ} (hq : 2≤q) (n : ℕ) :
    intervalMultiplicity (n-n/q) (q-1)+(n/q).choose 2 = intervalMultiplicity n q := by
  cases q with
  | zero => omega
  | succ q =>
    cases q with
    | zero => omega
    | succ q =>
      have h := bound_eq_intervalMultiplicity (q := q+2) (by omega) n
      change Bound (n-n/(q+2)) (q+1)+(n/(q+2)).choose 2 = _ at h
      rw [bound_eq_intervalMultiplicity (by omega : 1≤q+1)] at h
      simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel] using h

theorem ceil_split_cost {n q : ℕ} (hq : 2≤q) (hr : n%q≠0) :
    intervalMultiplicity (n-(n/q+1)) (q-1)+(n/q+1).choose 2 =
      intervalMultiplicity n q := by
  let D := n/q
  let r := n%q
  let m := n-(D+1)
  have hq1 : 1≤q := by omega
  have hq0 : 0<q := by omega
  have hr1 : 1≤r := by dsimp only [r]; omega
  have hrq : r<q := Nat.mod_lt n hq0
  have hdiv : q*D≤n := Nat.mul_div_le n q
  have hrem : q*D+r=n := by
    dsimp only [D, r]
    have hh := Nat.mod_add_div n q
    omega
  have htwoD : 2*D≤q*D := Nat.mul_le_mul_right D hq
  have hb : D+1≤n := by omega
  have hm : m+(D+1)=n := Nat.sub_add_cancel hb
  have hqsub : q-1+1=q := Nat.sub_add_cancel hq1
  have hqD : (q-1)*D+D=q*D := by
    have hh := congrArg (fun z : ℕ => z*D) hqsub
    simpa only [Nat.add_mul, one_mul] using hh
  have hml : (q-1)*D≤m := by omega
  have hmu : m≤(q-1)*(D+1) := by
    have he : (q-1)*(D+1)=(q-1)*D+(q-1) := by ring
    omega
  have hnhi : n≤q*(D+1) := (Nat.lt_mul_div_succ n hq0).le
  have hwhole := interval_window hq1 hdiv hnhi
  have hprefix := interval_window (by omega : 1≤q-1) hml hmu
  have hchoose := choose_two_twice (D+1)
  have hmD := congrArg (fun z : ℕ => 2*D*z) hm
  have hqDD := congrArg (fun z : ℕ => z*D*(D+1)) hqsub
  change intervalMultiplicity m (q-1)+(D+1).choose 2 = intervalMultiplicity n q
  nlinarith only [hwhole, hprefix, hchoose, hmD, hqDD]

theorem balanced_split_cost {n q b : ℕ} (hq : 2≤q) (hb : BalancedTail n q b) :
    intervalMultiplicity (n-b) (q-1)+b.choose 2 = intervalMultiplicity n q := by
  rcases hb with rfl | ⟨hr, rfl⟩
  · exact floor_split_cost hq n
  · exact ceil_split_cost hq hr

#print axioms floor_split_cost
#print axioms ceil_split_cost
#print axioms balanced_split_cost
end
end JSP233.APBalanced86412
