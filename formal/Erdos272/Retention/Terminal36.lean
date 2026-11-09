module

public import Erdos272.Resources.ExteriorWitness36
public import Erdos272.Core.CoreAP36
public import Erdos272.Retention.RestoreTerminal35
public import Erdos272.Retention.FringeRestore36

@[expose] public section

/-! Actual long-core terminals with automatic crooked witnesses.
The final retained and original-family endpoints have no witness, good-crooked
classification, totient/Hall supply or retained-cardinality premise. -/
namespace JSP233.Terminal36
open StarCompletion PrivatePairExistence StarResources30 StepHall33 LongTerminal35 ExteriorWitness36
open scoped Classical BigOperators
noncomputable section

theorem actual_root_large_with_reservation (N c L R : ℕ) (H : Finset (Finset ℤ))
    (I : Finset (ℕ×ℕ)) (hc : 1≤c) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hthin : 6*(L+N-R)*(Nat.log 2 N+1)≤N)
    (hv : ValidIntervals N c L R I) (hlegal : Legal (Ground N) (H∪Intervals I))
    (hroot : Rooted H (c:ℤ)) :
    H.card+(Reserved c N I).card≤(APSmall H).card+(c-1)/2+
      (PairUniverse (c:ℤ) (Ground N)).card := by
  have hH : Legal (Ground N) H :=
    ⟨fun S hS => hlegal.1 S (Finset.mem_union_left _ hS),
      fun S hS T hT he => hlegal.2 S (Finset.mem_union_left _ hS) T (Finset.mem_union_left _ hT) he⟩
  have hAP := CoreAP36.actual_core_root_AP_card N c L R (APLarge H) hc hcL hLR hRN
    (by nlinarith : 4*(L+N-R)*(Nat.log 2 N+1)≤N)
    (fun S hS => hH.1 S (Finset.mem_filter.mp hS).1)
    (fun S hS => (Finset.mem_filter.mp hS).2.1)
    (fun S hS => hroot S (Finset.mem_filter.mp hS).1)
    (fun S hS => (Finset.mem_filter.mp hS).2.2)
  have hC := crooked_outside_available_card hH hroot
    (actual_crooked_reserved_avoiding_witnesses N c L R H I hc hcL hLR hRN hthin hv hlegal hroot)
  have hp := actual_root_resources_with_reservation N c L R H I hc hLR hv hlegal hroot
  have hf := family_partition H
  change (APTriples H).card+(CoreAP36.CoreAPPairs N c L R (APLarge H)).card+
    (OutsideAvailable (c:ℤ) (Ground N) H (Reserved c N I)).card+(Reserved c N I).card≤
      (PairUniverse (c:ℤ) (Ground N)).card at hp
  omega

theorem actual_interval_terminal (N c L R : ℕ) (H : Finset (Finset ℤ))
    (I : Finset (ℕ×ℕ)) (hc : 1≤c) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hthin : 6*(L+N-R)*(Nat.log 2 N+1)≤N)
    (hv : ValidIntervals N c L R I) (hne : I.Nonempty)
    (hlegal : Legal (Ground N) (H∪Intervals I)) (hroot : Rooted H (c:ℤ)) :
    (H∪Intervals I).card≤N.choose 2+1 := by
  have hr := actual_root_large_with_reservation N c L R H I hc hcL hLR hRN hthin hv hlegal hroot
  have hs := actual_small_boundary_payment N c L R H I hc hLR hv hne hlegal hroot
  have hp := reserved_card_partition N c L R I hLR hv
  have hd : Disjoint H (Intervals I) := by
    apply Finset.disjoint_left.mpr
    intro S hS hI
    obtain ⟨p,hpI,rfl⟩ := Finset.mem_image.mp hI
    obtain ⟨hcp,_,_,_⟩ := hv p hpI
    have hh := hroot (Interval p) hS
    simp only [Interval,Finset.mem_Icc] at hh
    omega
  have hf : (H∪Intervals I).card=H.card+I.card := by
    rw [Finset.card_union_of_disjoint hd,intervals_card N c L R I hLR hv]
  have hcN : c≤N := by omega
  have hU : (PairUniverse (c:ℤ) (Ground N)).card=(N-1).choose 2 := by
    unfold PairUniverse
    rw [Finset.card_powersetCard,Finset.card_erase_of_mem ((mem_ground _ _).mpr ⟨by omega,by omega⟩),ground_card]
  have hchoose : N.choose 2=(N-1)+(N-1).choose 2 := by
    calc
      N.choose 2=((N-1)+1).choose (1+1) := by congr 1; omega
      _=(N-1).choose 1+(N-1).choose 2 := Nat.choose_succ_succ _ _
      _=(N-1)+(N-1).choose 2 := by simp
  rw [hU] at hr
  rw [hf,hchoose]
  have hdiv : (c-1)/2≤c-1 := Nat.div_le_self _ _
  omega

theorem actual_native_interval_terminal (N c L R : ℕ) (G : Finset (Finset ℤ))
    (hc : 1≤c) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hthin : 6*(L+N-R)*(Nat.log 2 N+1)≤N) (hlegal : Legal (Ground N) G)
    (hne : (Avoiders G (c:ℤ)).Nonempty)
    (hi : ∀ S∈Avoiders G (c:ℤ), ∃ a b : ℕ,
      c<a ∧ a≤L ∧ R≤b ∧ b≤N ∧ S=Interval (a,b)) : G.card≤N.choose 2+1 := by
  obtain ⟨I,hv,hIA,hG⟩ := actual_avoider_interval_encoding N c L R G hi
  have hI : I.Nonempty := by
    obtain ⟨S,hS⟩ := hne
    rw [←hIA] at hS
    obtain ⟨p,hp,_⟩ := Finset.mem_image.mp hS
    exact ⟨p,hp⟩
  have hroot : Rooted (RootPart G (c:ℤ)) (c:ℤ) := fun S hS => (Finset.mem_filter.mp hS).2
  have hlegal' : Legal (Ground N) (RootPart G (c:ℤ)∪Intervals I) := hG ▸ hlegal
  rw [hG]
  exact actual_interval_terminal N c L R (RootPart G (c:ℤ)) I hc hcL hLR hRN hthin hv hI hlegal' hroot

theorem actual_long_core_restore (N c L R : ℕ) (F G E : Finset (Finset ℤ))
    (hN : 1≤N) (hc : 1≤c) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hthin : 6*(L+N-R)*(Nat.log 2 N+1)≤N) (hfringe : 4640*(L+N-R)≤N)
    (hG : G=F\E) (hEF : E⊆F) (hlegal : Legal (Ground N) F)
    (hbad : ∀ S∈E, ¬IsAP S) (hdense : ∀ S∈E, N<16*S.card)
    (hne : (Avoiders G (c:ℤ)).Nonempty)
    (hi : ∀ S∈Avoiders G (c:ℤ), ∃ a b : ℕ,
      c<a ∧ a≤L ∧ R≤b ∧ b≤N ∧ S=Interval (a,b)) : F.card≤B N := by
  have hterminal := actual_native_interval_terminal N c L R G hc hcL hLR hRN hthin
    (RestoreTerminal35.retained_legal hG hlegal) hne hi
  have hcm := RestoreTerminal35.actual_interval_core_member N c L R G hLR hne hi
  have ht : ((L+N-R:ℕ):ℤ)=(L:ℤ)+(N:ℤ)-(R:ℤ) := by omega
  exact FringeRestore36.restore_from_proved_terminal N (L+N-R) F G E (L:ℤ) (R:ℤ)
    hN hG hEF hlegal hbad hdense hcm ht hfringe hterminal

#print axioms actual_root_large_with_reservation
#print axioms actual_interval_terminal
#print axioms actual_native_interval_terminal
#print axioms actual_long_core_restore
end
end JSP233.Terminal36
