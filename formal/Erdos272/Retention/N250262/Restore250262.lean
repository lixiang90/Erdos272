module

public import Erdos272.Retention.N250262.RecoveryChain250262
public import Erdos272.Retention.N250262.TerminalRatio250262

@[expose] public section

namespace JSP233.Restore250262
open StarCompletion APGeometry DenseDeletion40 TerminalDeficit51 HarmonicAbel29
open RootModel291012 RecoveryChain250262 LongTerminal35
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem minimum_payment {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T U : Finset ℤ}
    (g : Start N c L R F P T) (hN : 250262 ≤ N) (hhi : N ≤ 291011)
    (hU : U ∈ Omitted N c F) (hmin : ∀ S ∈ Omitted N c F, U.card ≤ S.card) :
    4*(U.card : ℝ)+4*Width N L R+4*(Omitted N c F).card < 5*N := by
  have hw := (final_bounds g hN (by omega : N ≤ 642498)).2
  have hcore := core g hN (by omega : N ≤ 642498)
  have hL : 1 ≤ L := by have hh := g.root_left; omega
  have hn : (250262 : ℝ) ≤ N := by exact_mod_cast hN
  have hsize : (U.card : ℝ) ≤ N := by
    exact_mod_cast (show U.card ≤ N by
      have hh := Finset.card_le_card (g.legal.1 U (omitted_subset hU)); rwa [ground_card] at hh)
  have hdense : ∀ tau : ℝ, tau*(N : ℝ) < U.card → ∀ S ∈ Omitted N c F, tau*(N : ℝ) < S.card := by
    intro tau ht S hS
    exact ht.trans_le (by exact_mod_cast hmin S hS)
  by_cases h34 : (3/4 : ℝ)*N < U.card
  · have he := FringePlans250262.rank2high hN hL g.left_right g.right_ground
      g.legal omitted_subset omitted_bad (hdense _ h34) hcore hw
    nlinarith only [he, hsize, hw, hn]
  have h34le : (U.card : ℝ) ≤ (3/4 : ℝ)*N := le_of_not_gt h34
  by_cases h12 : (1/2 : ℝ)*N < U.card
  · have he := FringePlans250262.rank2low hN hL g.left_right g.right_ground
      g.legal omitted_subset omitted_bad (hdense _ h12) hcore hw
    nlinarith only [he, h34le, hw, hn]
  have h12le : (U.card : ℝ) ≤ (1/2 : ℝ)*N := le_of_not_gt h12
  by_cases h13 : (1/3 : ℝ)*N < U.card
  · have he := FringePlans250262.rank3 hN hL g.left_right g.right_ground
      g.legal omitted_subset omitted_bad (hdense _ h13) hcore hw
    nlinarith only [he, h12le, hw, hn]
  have h13le : (U.card : ℝ) ≤ (1/3 : ℝ)*N := le_of_not_gt h13
  by_cases h14 : (1/4 : ℝ)*N < U.card
  · have he := FringePlans250262.rank4 hN hL g.left_right g.right_ground
      g.legal omitted_subset omitted_bad (hdense _ h14) hcore hw
    nlinarith only [he, h13le, hw, hn]
  have h14le : (U.card : ℝ) ≤ (1/4 : ℝ)*N := le_of_not_gt h14
  by_cases h15 : (1/5 : ℝ)*N < U.card
  · have he := FringePlans250262.rank5 hN hL g.left_right g.right_ground
      g.legal omitted_subset omitted_bad (hdense _ h15) hcore hw
    nlinarith only [he, h14le, hw, hn]
  have h15le : (U.card : ℝ) ≤ (1/5 : ℝ)*N := le_of_not_gt h15
  have he := FringePlans250262.rank6 hN hL g.left_right g.right_ground
    g.legal omitted_subset omitted_bad (strong_dense g hN (by omega : N ≤ 642498))
    hcore hw
  nlinarith only [he, h15le, hw, hn]

theorem actual_recovered_original {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 250262 ≤ N) (hhi : N ≤ 291011) : F.card ≤ B N := by
  let E := Omitted N c F
  let G := F\E
  have hEF : E ⊆ F := omitted_subset
  have hGF : G ⊆ F := Finset.sdiff_subset
  have hGlegal : Legal (Ground N) G :=
    ⟨fun S hS => g.legal.1 S (hGF hS), fun S hS U hU hSU => g.legal.2 S (hGF hS) U (hGF hU) hSU⟩
  have hcard : G.card+E.card = F.card := Finset.card_sdiff_add_card_eq_card hEF
  have hs := final_bounds g hN (by omega : N ≤ 642498)
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hc : 1 ≤ c := by exact_mod_cast ((mem_ground N (c : ℤ)).mp g.root_mem).1
  have hRN := g.right_ground
  let w := L+N-R
  have hw : (w : ℝ) = Width N L R := by
    dsimp only [w, Width]
    rw [Nat.cast_sub (by omega : R ≤ L+N)]
    push_cast
    ring
  have hthin : 2811*L+1193*(L+N-R) ≤ 192*N := by
    have ht : 2811*(L : ℝ)+1193*(w : ℝ) ≤ 192*N := by
      rw [hw]
      nlinarith only [hs.1, hs.2, hn]
    exact_mod_cast ht
  have havoiders : Avoiders G (c : ℤ) = Avoiders (Retained N 12 F) (c : ℤ) := by
    exact actual_avoider_readdition N 12 F (c : ℤ)
  have hi : ∀ S ∈ Avoiders G (c : ℤ), ∃ a b : ℕ,
      c<a ∧ a≤L ∧ R≤b ∧ b≤N ∧ S=Interval (a,b) := by
    rw [havoiders]
    exact RetainedIntervals250262.actual_avoiders_intervals g hN (by omega : N ≤ 642498) (by nlinarith only [hs.1, hn])
  have hne : (Avoiders G (c : ℤ)).Nonempty := by
    rw [havoiders]
    exact ⟨P, Finset.mem_filter.mpr ⟨g.right_member, g.right_avoids⟩⟩
  by_cases he : E.Nonempty
  · obtain ⟨U, hUE, hmin⟩ := Finset.exists_min_image E Finset.card he
    have hp := minimum_payment g hN hhi hUE hmin
    have ht := TerminalRatio250262.actual_native_terminal_deficit N c L R F G U
      (by omega : N < 510510) hc g.root_left g.left_right g.right_ground hthin
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
    have ht := TerminalRatio250262.actual_native_interval_terminal N c L R G
      (by omega : N < 510510) hc g.root_left g.left_right g.right_ground hthin hGlegal hne hi
    simp only [hE, Finset.card_empty, add_zero] at hcard
    unfold B
    omega

#print axioms minimum_payment
#print axioms actual_recovered_original
end
end JSP233.Restore250262
