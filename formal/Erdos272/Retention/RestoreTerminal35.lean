module

public import Erdos272.Retention.Restore33
public import Erdos272.Retention.LongTerminal35

@[expose] public section

/-! Actual thin-fringe recovery with a proved retained-family terminal.
No retained-family cardinality premise is supplied.  The remaining local
crooked geometry is exposed by `GoodCrooked`, not hidden in a number. -/
namespace JSP233.RestoreTerminal35
open StarCompletion LongTerminal35 Restore33
open scoped Classical
noncomputable section

theorem retained_legal {N : ℕ} {F G E : Finset (Finset ℤ)}
    (hG : G=F\E) (hlegal : Legal (Ground N) F) : Legal (Ground N) G := by
  have hGF : G⊆F := by rw [hG]; exact Finset.sdiff_subset
  exact ⟨fun S hS => hlegal.1 S (hGF hS),fun S hS T hT he => hlegal.2 S (hGF hS) T (hGF hT) he⟩

theorem interval_isAP (a b : ℕ) (hab : a≤b) : IsAP (Interval (a,b)) := by
  refine ⟨1,a,by omega,a,b,?_,Finset.mem_Icc.mpr ⟨le_rfl,by exact_mod_cast hab⟩⟩
  intro x
  simp only [Interval,Finset.mem_Icc,one_dvd,and_true]

theorem actual_interval_core_member (N c L R : ℕ) (G : Finset (Finset ℤ))
    (hLR : L≤R) (hne : (Avoiders G (c:ℤ)).Nonempty)
    (hi : ∀ S∈Avoiders G (c:ℤ), ∃ a b : ℕ,
      c<a ∧ a≤L ∧ R≤b ∧ b≤N ∧ S=Interval (a,b)) :
    ∃ H∈G, IsAP H ∧ Finset.Icc (L:ℤ) (R:ℤ)⊆H := by
  obtain ⟨S,hS⟩ := hne
  obtain ⟨a,b,_,haL,hRb,_,he⟩ := hi S hS
  refine ⟨S,(Finset.mem_filter.mp hS).1,he ▸ interval_isAP a b (by omega),?_⟩
  rw [he]
  intro x hx
  have hh := Finset.mem_Icc.mp hx
  exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩

theorem actual_long_core_restore_good_crooked (N c L R : ℕ)
    (F G E : Finset (Finset ℤ)) (hN : 1≤N) (hc : 1≤c) (hcL : c<L)
    (hLR : L≤R) (hRN : R≤N) (hJ : 19≤Nat.log 2 N+1)
    (hcore : 256*(L+N-R)*(Nat.log 2 N+1)≤N)
    (hG : G=F\E) (hEF : E⊆F) (hlegal : Legal (Ground N) F)
    (hbad : ∀ S∈E, ¬IsAP S) (hdense : ∀ S∈E, N<16*S.card)
    (hne : (Avoiders G (c:ℤ)).Nonempty)
    (hi : ∀ S∈Avoiders G (c:ℤ), ∃ a b : ℕ,
      c<a ∧ a≤L ∧ R≤b ∧ b≤N ∧ S=Interval (a,b))
    (hgood : ∀ S∈RootPart G (c:ℤ), ¬IsAP S → GoodCrooked c L R S) :
    F.card≤B N := by
  have hGcard := actual_native_interval_terminal_good_crooked N c L R G hc hcL hLR hRN hcore
    (retained_legal hG hlegal) hne hi hgood
  have hcm := actual_interval_core_member N c L R G hLR hne hi
  have ht : ((L+N-R:ℕ):ℤ)=(L:ℤ)+(N:ℤ)-(R:ℤ) := by omega
  exact actual_thin_fringe_restore N (L+N-R) (Nat.log 2 N+1) F G E (L:ℤ) (R:ℤ)
    hN hJ hG hEF hlegal hbad hdense hcm ht hcore hGcard

theorem actual_long_core_restore_crooked_triples (N c L R : ℕ)
    (F G E : Finset (Finset ℤ)) (hN : 1≤N) (hc : 1≤c) (hcL : c<L)
    (hLR : L≤R) (hRN : R≤N) (hJ : 19≤Nat.log 2 N+1)
    (hcore : 256*(L+N-R)*(Nat.log 2 N+1)≤N)
    (hG : G=F\E) (hEF : E⊆F) (hlegal : Legal (Ground N) F)
    (hbad : ∀ S∈E, ¬IsAP S) (hdense : ∀ S∈E, N<16*S.card)
    (hne : (Avoiders G (c:ℤ)).Nonempty)
    (hi : ∀ S∈Avoiders G (c:ℤ), ∃ a b : ℕ,
      c<a ∧ a≤L ∧ R≤b ∧ b≤N ∧ S=Interval (a,b))
    (hsmall : ∀ S∈RootPart G (c:ℤ), ¬IsAP S → S.card≤3) : F.card≤B N := by
  exact actual_long_core_restore_good_crooked N c L R F G E hN hc hcL hLR hRN hJ hcore
    hG hEF hlegal hbad hdense hne hi (fun S hS hbadS => Or.inl (hsmall S hS hbadS))

theorem actual_long_core_restore_left_crooked (N c L R : ℕ)
    (F G E : Finset (Finset ℤ)) (hN : 1≤N) (hc : 1≤c) (hcL : c<L)
    (hLR : L≤R) (hRN : R≤N) (hJ : 19≤Nat.log 2 N+1)
    (hcore : 256*(L+N-R)*(Nat.log 2 N+1)≤N)
    (hG : G=F\E) (hEF : E⊆F) (hlegal : Legal (Ground N) F)
    (hbad : ∀ S∈E, ¬IsAP S) (hdense : ∀ S∈E, N<16*S.card)
    (hne : (Avoiders G (c:ℤ)).Nonempty)
    (hi : ∀ S∈Avoiders G (c:ℤ), ∃ a b : ℕ,
      c<a ∧ a≤L ∧ R≤b ∧ b≤N ∧ S=Interval (a,b))
    (hleft : ∀ S∈RootPart G (c:ℤ), ¬IsAP S → ∃ a∈S, a<(c:ℤ)) : F.card≤B N := by
  exact actual_long_core_restore_good_crooked N c L R F G E hN hc hcL hLR hRN hJ hcore
    hG hEF hlegal hbad hdense hne hi (fun S hS hbadS => Or.inr (Or.inl (hleft S hS hbadS)))

#print axioms retained_legal
#print axioms interval_isAP
#print axioms actual_interval_core_member
#print axioms actual_long_core_restore_good_crooked
#print axioms actual_long_core_restore_crooked_triples
#print axioms actual_long_core_restore_left_crooked
end
end JSP233.RestoreTerminal35
