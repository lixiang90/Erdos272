module

public import Erdos272.Retention.RankTwenty58
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

/-! The real r11 restore table, using the pre-existing ratio-rank physical
payment theorem.  The original family and all deleted avoiders stay internal.
No new thin-fringe or endpoint price is supplied to the physical theorem. -/
namespace JSP233.Restore11Ratio112
open RankTwenty58 StarCompletion LongTerminal35 DenseDeletion40 JointFringe44
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0

def RankWidth11 : ℕ→ℕ
  | 2=>3 | 3=>4 | 4=>5 | 5=>7 | 6=>8 | 7=>9
  | 8=>11 | 9=>12 | 10=>13 | 11=>14 | _=>14

theorem rank_width11_ratio_payments : RatioRankTable 11 154 3 14 RankWidth11 := by
  intro k hk
  obtain ⟨h2,h11⟩ := Finset.mem_Icc.mp hk
  interval_cases k <;> decide

theorem actual_ratio11_physical_payments {N t : ℕ}
    (hsize : 14^3≤N) (hpay : 154*t≤3*N) :
    42*t≤N ∧
      (∀k∈Finset.Icc 2 11,k<RankWidth11 k ∧ 3≤RankWidth11 k) ∧
      (∀k∈Finset.Icc 2 11,(RankWidth11 k)^3≤N) ∧
      (∀k∈Finset.Icc 2 11,k*RankWidth11 k*t≤(RankWidth11 k-k)*N) ∧
      (∀k∈Finset.Icc 2 11,4*(k-1)*(JointCount (RankWidth11 k)+1)*t≤(5*k-9)*N) := by
  exact ratio_rank_physical_payments rank_width11_ratio_payments
    (by decide : 0<3) (by decide : 42*3≤154) hsize hpay

theorem actual_adaptive_restore11_ratio
    (N c L R : ℕ) (F G E : Finset (Finset ℤ))
    (hN : N<2^50) (hsize : 14^3≤N)
    (hc : 1≤c) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hpay : 154*(L+N-R)≤3*N)
    (hG : G=F\E) (hEF : E⊆F) (hlegal : Legal (Ground N) F)
    (hbad : ∀S∈E,¬IsAP S) (hdense : ∀S∈E,N<11*S.card)
    (havoid : ∀S∈E,(c:ℤ)∉S)
    (hne : (Avoiders G (c:ℤ)).Nonempty)
    (hi : ∀S∈Avoiders G (c:ℤ),∃a b:ℕ,
      c<a ∧ a≤L ∧ R≤b ∧ b≤N ∧ S=Interval (a,b)) : F.card≤B N := by
  exact actual_adaptive_restore_ratio 11 154 3 14 RankWidth11 N c L R F G E hN
    (by decide) (by decide) (by decide) rank_width11_ratio_payments hsize
    hc hcL hLR hRN hpay hG hEF hlegal hbad hdense havoid hne hi

theorem actual_deleted_avoider_restore11_ratio
    (N c L R : ℕ) (F : Finset (Finset ℤ))
    (hN : N<2^50) (hsize : 14^3≤N)
    (hc : 1≤c) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hpay : 154*(L+N-R)≤3*N)
    (hlegal : Legal (Ground N) F)
    (hne : (Avoiders (Retained N 11 F) (c:ℤ)).Nonempty)
    (hi : ∀S∈Avoiders (Retained N 11 F) (c:ℤ),∃a b:ℕ,
      c<a ∧ a≤L ∧ R≤b ∧ b≤N ∧ S=Interval (a,b)) : F.card≤B N := by
  exact actual_deleted_avoider_restore_ratio 11 154 3 14 RankWidth11 N c L R F hN
    (by decide) (by decide) (by decide) rank_width11_ratio_payments hsize
    hc hcL hLR hRN hpay hlegal hne hi

#print axioms rank_width11_ratio_payments
#print axioms actual_ratio11_physical_payments
#print axioms actual_adaptive_restore11_ratio
#print axioms actual_deleted_avoider_restore11_ratio
end
end JSP233.Restore11Ratio112
