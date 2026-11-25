module

public import Erdos272.Counting.N94488.HalfTrace94488
public import Erdos272.Core.N86412.Terminal86412
public import Erdos272.Retention.N82426.PointRecoveryCore82426

@[expose] public section

set_option Elab.async false

namespace JSP233.PointRecovery82426
open StarCompletion APGeometry DenseDeletion40 TerminalDeficit51 HarmonicAbel29
open RootModel291012 PointRecovery82426 LongTerminal35 LocalRecovery82427
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem deficit_card_bound {n kept omitted total member width : ℕ}
    (hcard : kept+omitted=total)
    (hterminal : kept+n≤n.choose 2+member+width)
    (hpayment : 4*(member : ℝ)+4*(width : ℝ)+4*(omitted : ℝ)<5*(n : ℝ)) :
    total≤B n := by
  have hterminalR : (kept : ℝ)+n≤(n.choose 2 : ℝ)+member+width := by
    exact_mod_cast hterminal
  have hcardR : (kept : ℝ)+omitted=total := by exact_mod_cast hcard
  have hquarter : 4*(total : ℝ)<4*(n.choose 2 : ℝ)+n := by
    linarith only [hterminalR, hcardR, hpayment]
  have hquarterN : 4*total<4*n.choose 2+n := by exact_mod_cast hquarter
  unfold B
  omega

theorem interval_card_bound {n total : ℕ} (h : total≤n.choose 2+1) : total≤B n := by
  unfold B
  omega

theorem minimum_payment {c L R : ℕ} {F : Finset (Finset ℤ)} {P T U : Finset ℤ}
    (g : Start 82426 c L R F P T)
    (hU : U∈Omitted 82426 c F) (hmin : ∀ S∈Omitted 82426 c F, U.card≤S.card) :
    4*(U.card : ℝ)+4*Width 82426 L R+4*(Omitted 82426 c F).card<5*82426 := by
  have hn : (0 : ℝ)<82426 := by exact_mod_cast (show 0<82426 by omega)
  have hs := final_bounds g
  by_cases hsmall : (U.card : ℝ)≤(82426 : ℝ)/3
  · have he := prepared g
    nlinarith only [hsmall, he, hs.2, hn]
  · have hdense : ∀ S∈Omitted 82426 c F, (1/3 : ℝ)*82426<S.card := by
      intro S hS
      have hm : (U.card : ℝ)≤S.card := by exact_mod_cast hmin S hS
      have hu : (82426 : ℝ)/3<U.card := lt_of_not_ge hsmall
      nlinarith only [hm, hu]
    have he := FringePlans109474.preparation (by omega : 901≤82426)
      (by have h:=g.root_left; omega) g.left_right g.right_ground g.legal
      omitted_subset omitted_bad hdense (core g) (strong g).2
    have hp := HalfTrace94488.actual_minimum_payment (by omega : 160≤82426)
      (by have h:=g.root_left; omega) g.left_right g.right_ground g.legal
      omitted_subset omitted_bad (core g) hU hmin hs.2.le
      (by simpa only [sub_eq_add_neg, neg_div] using he)
    exact (lt_add_of_pos_right _ (by norm_num : (0 : ℝ)<8)).trans
      (by simpa only [Nat.cast_ofNat] using hp)

theorem actual_recovered_prefix {c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start 82426 c L R F P T) : F.card ≤ B 82426 := by
  let E := Omitted 82426 c F
  let G := F\E
  have hEF : E ⊆ F := omitted_subset
  have hGF : G ⊆ F := Finset.sdiff_subset
  have hGlegal : Legal (Ground 82426) G :=
    ⟨fun S hS => g.legal.1 S (hGF hS), fun S hS U hU hSU => g.legal.2 S (hGF hS) U (hGF hU) hSU⟩
  have hcard : G.card+E.card = F.card := Finset.card_sdiff_add_card_eq_card hEF
  have hs := final_bounds g
  have hn : (0 : ℝ) < 82426 := by exact_mod_cast (show 0 < 82426 by omega)
  have hc : 1 ≤ c := by exact_mod_cast ((mem_ground 82426 (c : ℤ)).mp g.root_mem).1
  have hRN := g.right_ground
  let w := L+82426-R
  have hw : (w : ℝ) = Width 82426 L R := by
    dsimp only [w, Width]
    rw [Nat.cast_sub (by omega : R ≤ L+82426)]
    push_cast
    ring
  have hnative := native_gates g
  have havoiders : Avoiders G (c : ℤ) = Avoiders (Retained 82426 12 F) (c : ℤ) := by
    exact actual_avoider_readdition 82426 12 F (c : ℤ)
  have hi : ∀ S ∈ Avoiders G (c : ℤ), ∃ a b : ℕ,
      c<a ∧ a≤L ∧ R≤b ∧ b≤82426 ∧ S=Interval (a,b) := by
    rw [havoiders]
    exact RetainedIntervals86412.actual_avoiders_intervals g (by omega : 56400 ≤ 82426)
      (by omega : 82426 ≤ 88403) (by nlinarith only [hs.1, hn])
  have hne : (Avoiders G (c : ℤ)).Nonempty := by
    rw [havoiders]
    exact ⟨P, Finset.mem_filter.mpr ⟨g.right_member, g.right_avoids⟩⟩
  by_cases he : E.Nonempty
  · obtain ⟨U, hUE, hmin⟩ := Finset.exists_min_image E Finset.card he
    have hp := minimum_payment g hUE hmin
    have ht := Terminal86412.actual_native_terminal_deficit 82426 c L R F G U
      (by omega : 160≤82426) (by omega : 82426 < 120120) hc g.root_left g.left_right g.right_ground hnative
      g.legal hGF (hEF hUE) (Finset.mem_filter.mp hUE).2 hi
    rw [←hw] at hp
    exact deficit_card_bound hcard ht (by simpa only [Nat.cast_ofNat] using hp)
  · have hE : E = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
    have ht := Terminal86412.actual_native_interval_terminal 82426 c L R G
      (by omega : 160≤82426) (by omega : 82426 < 120120) hc g.root_left g.left_right g.right_ground hnative hGlegal hne hi
    simp only [hE, Finset.card_empty, add_zero] at hcard
    rw [hcard] at ht
    exact interval_card_bound ht

theorem actual_recovered_original {c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start 82426 c L R F P T) : F.card≤B 82426 :=
  actual_recovered_prefix g


#print axioms deficit_card_bound
#print axioms interval_card_bound
#print axioms minimum_payment
#print axioms actual_recovered_prefix
#print axioms actual_recovered_original
end
end JSP233.PointRecovery82426
