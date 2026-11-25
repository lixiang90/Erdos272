module

public import Erdos272.Core.N65968.IntervalTerminal65968
public import Erdos272.Resources.N291012.RootModel291012

@[expose] public section

/-! Restore the actual omitted family once its cardinality and the
positions of the surviving root avoiders have been bounded. The same
formula includes an empty omitted family. -/
namespace JSP233.DirectRestore20258
open StarCompletion RootModel291012 DenseDeletion40 TerminalDeficit51 LongTerminal35
open scoped Classical
noncomputable section
set_option autoImplicit false

theorem restored_card {N w size kept omitted : ℕ} (hN : 1 ≤ N)
    (hpart : kept+omitted = size) (hkept : kept ≤ N.choose 2+1)
    (homit : omitted+1 ≤ w) (hw : 4*w ≤ N+3) : size ≤ B N := by
  unfold B
  omega

theorem actual_restore_with_supply {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 160 ≤ N) (hhi : N < 120120)
    (hs : ShortSupply20258.AtRoot N c L R)
    (hcount : (Omitted N c F).card+1 ≤ L+(N-R)) (hw : 4*(L+(N-R)) ≤ N+3)
    (hi : ∀ S ∈ Avoiders (Retained N 12 F) (c : ℤ), ∃ a b : ℕ,
      c<a ∧ a≤L ∧ R≤b ∧ b≤N ∧ S=Interval (a,b)) : F.card ≤ B N := by
  let E := Omitted N c F
  let G := F \ E
  have hsub : E ⊆ F := (Finset.filter_subset _ _).trans (actual_deleted_subset N 12 F)
  have hGF : G ⊆ F := Finset.sdiff_subset
  have hLG : Legal (Ground N) G :=
    ⟨fun S hS => g.legal.1 S (hGF hS),fun S hS U hU => g.legal.2 S (hGF hS) U (hGF hU)⟩
  have he : Avoiders G (c : ℤ) = Avoiders (Retained N 12 F) (c : ℤ) :=
    actual_avoider_readdition N 12 F (c : ℤ)
  have hne : (Avoiders G (c : ℤ)).Nonempty := by
    rw [he]
    exact ⟨P,Finset.mem_filter.mpr ⟨g.right_member,g.right_avoids⟩⟩
  have hc : 1 ≤ c := by exact_mod_cast ((mem_ground N (c : ℤ)).mp g.root_mem).1
  have ht := Terminal65968.actual_native_interval_terminal_at N c L R G hN
    hhi hc g.root_left g.left_right g.right_ground hs hLG hne (he ▸ hi)
  exact restored_card (by omega) (Finset.card_sdiff_add_card_eq_card hsub) ht hcount hw

theorem actual_direct_restore {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 11400 ≤ N) (hhi : N < 120120)
    (hp : ShortSupplyProfile20258.profile L (N-R : ℕ) c ≤ ShortSupplyProfile20258.price*N+884)
    (hcount : (Omitted N c F).card+1 ≤ L+(N-R)) (hw : 4*(L+(N-R)) ≤ N+3)
    (hi : ∀ S ∈ Avoiders (Retained N 12 F) (c : ℤ), ∃ a b : ℕ,
      c<a ∧ a≤L ∧ R≤b ∧ b≤N ∧ S=Interval (a,b)) : F.card ≤ B N :=
  actual_restore_with_supply g (by omega) hhi
    (ShortSupply20258.of_profile hN hhi g.root_left g.left_right g.right_ground hp) hcount hw hi

end
end JSP233.DirectRestore20258
