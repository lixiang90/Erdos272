import Erdos272.Retention.Restore33

/-! Separate the deleted-fringe recovery cost from the long-core geometry.
Only 4640*t <= N is needed here; no logarithmic long-core condition occurs. -/
namespace JSP233.FringeRestore36
open StarCompletion ThinFringe33 KKRetention32 Restore33
open scoped Classical
noncomputable section

theorem fringe_quarter_payment (N t : ℕ) (hN : 1≤N) (hthin : 4640*t≤N) :
    1160*(t-1)≤(N-1)/4 := by
  apply (Nat.le_div_iff_mul_le (by decide : 0<4)).mpr
  by_cases ht : t=0
  · simp [ht]
  · omega

theorem actual_deleted_fringe_quarter (N t : ℕ) (F G E : Finset (Finset ℤ)) (L R : ℤ)
    (hN : 1≤N) (hG : G=F\E) (hEF : E⊆F)
    (hlegal : Legal (Ground N) F) (hbad : ∀ S∈E, ¬IsAP S)
    (hdense : ∀ S∈E, N<16*S.card)
    (hcoreG : ∃ H∈G, IsAP H ∧ Finset.Icc L R⊆H)
    (ht : (t:ℤ)=L+(N:ℤ)-R) (hthin : 4640*t≤N) : E.card≤(N-1)/4 := by
  have hthin0 : 256*t≤N := by omega
  obtain ⟨hL,hLR,hR,hcoreF⟩ := retained_interval_geometry N t F G E L R
    hG hlegal hcoreG ht hthin0
  exact (actual_dense_fringe_bound_of_length N t F E L R hlegal hEF hbad hdense
    hL hLR hR hcoreF ht hthin0).trans (fringe_quarter_payment N t hN hthin)

theorem restore_from_proved_terminal (N t : ℕ) (F G E : Finset (Finset ℤ)) (L R : ℤ)
    (hN : 1≤N) (hG : G=F\E) (hEF : E⊆F)
    (hlegal : Legal (Ground N) F) (hbad : ∀ S∈E, ¬IsAP S)
    (hdense : ∀ S∈E, N<16*S.card)
    (hcoreG : ∃ H∈G, IsAP H ∧ Finset.Icc L R⊆H)
    (ht : (t:ℤ)=L+(N:ℤ)-R) (hthin : 4640*t≤N)
    (hterminal : G.card≤N.choose 2+1) : F.card≤B N := by
  have hE := actual_deleted_fringe_quarter N t F G E L R hN hG hEF hlegal hbad
    hdense hcoreG ht hthin
  have hc := deletion_card_exact F E hEF
  rw [←hG] at hc
  unfold B
  omega

#print axioms fringe_quarter_payment
#print axioms actual_deleted_fringe_quarter
#print axioms restore_from_proved_terminal
end
end JSP233.FringeRestore36
