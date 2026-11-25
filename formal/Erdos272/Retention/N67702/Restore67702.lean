module

public import Erdos272.Retention.N67702.RecoveryChain67702
public import Erdos272.Resources.N67702.MinimumPaymentWide67702
public import Erdos272.Core.N86412.Terminal86412

@[expose] public section

namespace JSP233.Restore67702
open StarCompletion APGeometry DenseDeletion40 TerminalDeficit51 HarmonicAbel29
open RootModel291012 RecoveryChain67702 LongTerminal35
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem minimum_payment {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T U : Finset ℤ}
    (g : Start N c L R F P T) (hN : 67702≤N) (hhi : N≤80469)
    (hU : U∈Omitted N c F) (hmin : ∀ S∈Omitted N c F,U.card≤S.card) :
    4*(U.card : ℝ)+4*Width N L R+4*(Omitted N c F).card<5*N := by
  have hw : Width N L R < (11/100 : ℝ)*N := by
    have hb := (final_bounds g hN hhi).2
    have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    nlinarith only [hb,hn]
  have hp := MinimumPaymentWide67702.actual_minimum_payment (by omega : 160≤N)
    (by have h:=g.root_left; omega) g.left_right g.right_ground g.legal
    omitted_subset omitted_bad (core g hN hhi) hU hmin hw
    (prepared g hN hhi)
  linarith only [hp]

theorem actual_recovered_original {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 67702≤N) (hhi : N≤80469) : F.card ≤ B N := by
  let E := Omitted N c F
  let G := F\E
  have hEF : E ⊆ F := omitted_subset
  have hGF : G ⊆ F := Finset.sdiff_subset
  have hGlegal : Legal (Ground N) G :=
    ⟨fun S hS => g.legal.1 S (hGF hS), fun S hS U hU hSU => g.legal.2 S (hGF hS) U (hGF hU) hSU⟩
  have hcard : G.card+E.card = F.card := Finset.card_sdiff_add_card_eq_card hEF
  have hs := final_bounds g hN hhi
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hc : 1 ≤ c := by exact_mod_cast ((mem_ground N (c : ℤ)).mp g.root_mem).1
  have hRN := g.right_ground
  let w := L+N-R
  have hw : (w : ℝ) = Width N L R := by
    dsimp only [w, Width]
    rw [Nat.cast_sub (by omega : R ≤ L+N)]
    push_cast
    ring
  have hnative := native_gates g hN hhi
  have havoiders : Avoiders G (c : ℤ) = Avoiders (Retained N 12 F) (c : ℤ) := by
    exact actual_avoider_readdition N 12 F (c : ℤ)
  have hi : ∀ S ∈ Avoiders G (c : ℤ), ∃ a b : ℕ,
      c<a ∧ a≤L ∧ R≤b ∧ b≤N ∧ S=Interval (a,b) := by
    rw [havoiders]
    exact RetainedIntervals67702.actual_avoiders_intervals g (by omega : 56400 ≤ N)
      (by omega : N ≤ 88403) (by nlinarith only [hs.1, hn])
  have hne : (Avoiders G (c : ℤ)).Nonempty := by
    rw [havoiders]
    exact ⟨P, Finset.mem_filter.mpr ⟨g.right_member, g.right_avoids⟩⟩
  by_cases he : E.Nonempty
  · obtain ⟨U, hUE, hmin⟩ := Finset.exists_min_image E Finset.card he
    have hp := minimum_payment g hN hhi hUE hmin
    have ht := Terminal86412.actual_native_terminal_deficit N c L R F G U
      (by omega : 160≤N) (by omega : N < 120120) hc g.root_left g.left_right g.right_ground hnative
      g.legal hGF (hEF hUE) (Finset.mem_filter.mp hUE).2 hi
    have htR : (G.card : ℝ)+N ≤ (N.choose 2 : ℝ)+U.card+(w : ℝ) := by exact_mod_cast ht
    have hcardR : (G.card : ℝ)+E.card = F.card := by exact_mod_cast hcard
    have hquarter : 4*(F.card : ℝ) < 4*(N.choose 2 : ℝ)+N := by
      rw [←hw] at hp
      linarith only [htR, hcardR, hp]
    have hquarterN : 4*F.card < 4*N.choose 2+N := by exact_mod_cast hquarter
    unfold B
    omega
  · have hE : E = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
    have ht := Terminal86412.actual_native_interval_terminal N c L R G
      (by omega : 160≤N) (by omega : N < 120120) hc g.root_left g.left_right g.right_ground hnative hGlegal hne hi
    simp only [hE, Finset.card_empty, add_zero] at hcard
    unfold B
    omega

#print axioms minimum_payment
#print axioms actual_recovered_original
end
end JSP233.Restore67702
