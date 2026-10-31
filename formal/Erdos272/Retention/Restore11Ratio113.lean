import Erdos272.Retention.CeilFringe113
import Erdos272.Retention.Restore11Ratio112

/-! Same-original-family r11 restoration at ratio 1120/23. Only the actual
minimum-rank-eleven branch needs the changed ceil/private physical labels. -/
namespace JSP233.Restore11Ratio113
open StarCompletion APGeometry LongTerminal35 DenseDeletion40 JointFringe44
open QuarterRestore54 RankTwenty58 KKRetention32 Restore33 ThinFringe33
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

theorem lower_rank_ratio_table :
    RatioRankTable 10 1120 23 13 Restore11Ratio112.RankWidth11 := by
  intro k hk
  obtain ⟨h2,h10⟩ := Finset.mem_Icc.mp hk
  interval_cases k <;> decide

theorem actual_adaptive_restore11_ratio
    (N c L R : ℕ) (F G E : Finset (Finset ℤ))
    (hN : N<2^50) (hsize : 26000≤N)
    (hc : 1≤c) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hpay : 1120*(L+N-R)≤23*N)
    (hG : G=F\E) (hEF : E⊆F) (hlegal : Legal (Ground N) F)
    (hbad : ∀S∈E,¬IsAP S) (hdense : ∀S∈E,N<11*S.card)
    (havoid : ∀S∈E,(c:ℤ)∉S)
    (hne : (Avoiders G (c:ℤ)).Nonempty)
    (hi : ∀S∈Avoiders G (c:ℤ),∃a b:ℕ,
      c<a ∧ a≤L ∧ R≤b ∧ b≤N ∧ S=Interval (a,b)) : F.card≤B N := by
  have hGF : G⊆F := by rw [hG];exact Finset.sdiff_subset
  have hthin : 42*(L+N-R)≤N := by omega
  have hgeometry : 165*(L+N-R)≤4*N := by omega
  have hGlegal := RestoreTerminal35.retained_legal hG hlegal
  have ht := TerminalSeven52.actual_native_interval_terminal N c L R G hN hc hcL hLR hRN
    hthin hGlegal hne hi
  have hcard := deletion_card_exact F E hEF
  rw [←hG] at hcard
  by_cases he : E.Nonempty
  · obtain ⟨P,hPE,hmin⟩ := Finset.exists_min_image E Finset.card he
    by_cases hm : 10*P.card≤N
    · by_cases hlarge : 90<L+N-R
      · obtain ⟨H,hHG,hHAP,hKH⟩ := RestoreTerminal35.actual_interval_core_member N c L R G hLR hne hi
        have hb := CeilFringe113.actual_dense_fringe_bound55 (by omega : 225≤N)
          (by omega : 1≤L) hLR hRN hlarge hlegal hEF hbad hdense
          ⟨H,hGF hHG,hHAP,hKH⟩ hgeometry
        have hext := ground_interval_exterior_card N (by exact_mod_cast (show 1≤L by omega) : (1:ℤ)≤L)
          (by exact_mod_cast hLR : (L:ℤ)≤R) (by exact_mod_cast hRN : (R:ℤ)≤N)
        have hout : (Ground N\Finset.Icc (L:ℤ) (R:ℤ)).card≤L+N-R := by omega
        have he' : E.card≤55*(L+N-R) := hb.trans (Nat.mul_le_mul_left _ hout)
        have hd := TerminalSeven52.actual_native_terminal_deficit N c L R F G P hN hc hcL hLR hRN
          hthin hlegal hGF (hEF hPE) (havoid P hPE) hi
        have hquarter : 4*10*(55+1)*(L+N-R)≤(5*10-4)*N := by omega
        exact card_le_B_of_four_card (reciprocal_quarter_payment (by decide : 0<10)
          hm hd he' hcard hquarter)
      · have hb := TerminalDeficit51.actual_interval_fringe_count 11 15 N c L R F G E
          (by decide) (by decide) (by decide) (by norm_num;omega) hc hcL hLR hRN
          hgeometry hGF hEF hlegal hbad hdense hne hi
        have hj : JointCount 15=59 := by norm_num [JointCount,ShortCount,Finset.sum_Icc_succ_top]
        rw [hj] at hb
        have hp := quarter_payment 59 N (L+N-R) (by omega) (by omega)
        unfold B
        omega
    · have hd10 : ∀S∈E,N<10*S.card := by
        intro S hS
        have hmul := Nat.mul_le_mul_left 10 (hmin S hS)
        omega
      exact RankTwenty58.actual_adaptive_restore_ratio 10 1120 23 13
        Restore11Ratio112.RankWidth11 N c L R F G E hN (by decide) (by decide)
        (by decide) lower_rank_ratio_table (by norm_num;omega) hc hcL hLR hRN hpay
        hG hEF hlegal hbad hd10 havoid hne hi
  · have hE : E=∅ := Finset.not_nonempty_iff_eq_empty.mp he
    simp only [hE,Finset.card_empty,add_zero] at hcard
    unfold B
    omega

theorem actual_deleted_avoider_restore11_ratio
    (N c L R : ℕ) (F : Finset (Finset ℤ))
    (hN : N<2^50) (hsize : 26000≤N)
    (hc : 1≤c) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hpay : 1120*(L+N-R)≤23*N)
    (hlegal : Legal (Ground N) F)
    (hne : (Avoiders (Retained N 11 F) (c:ℤ)).Nonempty)
    (hi : ∀S∈Avoiders (Retained N 11 F) (c:ℤ),∃a b:ℕ,
      c<a ∧ a≤L ∧ R≤b ∧ b≤N ∧ S=Interval (a,b)) : F.card≤B N := by
  let E := TerminalDeficit51.OmittedAvoiders N 11 F (c:ℤ)
  have hEF : E⊆F := (Finset.filter_subset _ _).trans (actual_deleted_subset N 11 F)
  have ha := TerminalDeficit51.actual_avoider_readdition N 11 F (c:ℤ)
  apply actual_adaptive_restore11_ratio N c L R F (F\E) E hN hsize hc hcL hLR hRN hpay
    rfl hEF hlegal
  · intro S hS
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).2.1
  · intro S hS
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).2.2
  · intro S hS
    exact (Finset.mem_filter.mp hS).2
  · simpa only [E,ha] using hne
  · simpa only [E,ha] using hi

#print axioms lower_rank_ratio_table
#print axioms actual_adaptive_restore11_ratio
#print axioms actual_deleted_avoider_restore11_ratio
end
end JSP233.Restore11Ratio113
