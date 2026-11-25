module

public import Erdos272.Foundation.APGeometry

@[expose] public section

namespace JSP233.APCoatom65172
open StarCompletion APGeometry
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem missing_force {P Q : Finset ℤ} {x y : ℤ}
    (hmiss : (P\Q).card≤1) (hx : x∈P) (hxQ : x∉Q)
    (hy : y∈P) (hne : y≠x) : y∈Q := by
  by_contra hyQ
  exact hne (Finset.card_le_one.mp hmiss y (Finset.mem_sdiff.mpr ⟨hy,hyQ⟩)
    x (Finset.mem_sdiff.mpr ⟨hx,hxQ⟩))

theorem retained_adjacent {P Q : Finset ℤ} {d p : ℤ}
    (hP : APAt d p P) (hfour : 4≤P.card) (hmiss : (P\Q).card≤1) :
    ∃ u : ℤ, u∈P∩Q ∧ u+d∈P∩Q := by
  obtain ⟨a,b,ha,ha1,hb,_hbounds,hspan⟩ := apAt_adjacent_min hP (by omega : 2≤P.card)
  have hd : 0<d := hP.1
  have hc : (4 : ℤ)≤(P.card : ℤ) := by exact_mod_cast hfour
  have h3 : a+d+d+d≤b := by
    have hh := mul_le_mul_of_nonneg_left (show (3 : ℤ)≤(P.card : ℤ)-1 by omega) hd.le
    nlinarith only [hh,hspan]
  have ha2 : a+d+d∈P := apAt_fill hP ha hb
    (by omega) (by omega) ⟨2,by ring⟩
  have ha3 : a+d+d+d∈P := apAt_fill hP ha hb
    (by omega) h3 ⟨3,by ring⟩
  by_cases haQ : a∈Q
  · by_cases ha1Q : a+d∈Q
    · exact ⟨a,Finset.mem_inter.mpr ⟨ha,haQ⟩,Finset.mem_inter.mpr ⟨ha1,ha1Q⟩⟩
    · have h2 := missing_force hmiss ha1 ha1Q ha2 (by omega : a+d+d≠a+d)
      have h3Q := missing_force hmiss ha1 ha1Q ha3 (by omega : a+d+d+d≠a+d)
      exact ⟨a+d+d,Finset.mem_inter.mpr ⟨ha2,h2⟩,Finset.mem_inter.mpr ⟨ha3,h3Q⟩⟩
  · have h1 := missing_force hmiss ha haQ ha1 (by omega : a+d≠a)
    have h2 := missing_force hmiss ha haQ ha2 (by omega : a+d+d≠a)
    exact ⟨a+d,Finset.mem_inter.mpr ⟨ha1,h1⟩,Finset.mem_inter.mpr ⟨ha2,h2⟩⟩

theorem step_divides {P Q : Finset ℤ} {d p e q : ℤ}
    (hP : APAt d p P) (hQ : APAt e q Q)
    (hfour : 4≤P.card) (hmiss : (P\Q).card≤1) : e∣d := by
  obtain ⟨u,hu,hu1⟩ := retained_adjacent hP hfour hmiss
  have hh := apAt_dvd_sub hQ (Finset.mem_inter.mp hu).2 (Finset.mem_inter.mp hu1).2
  have he : u+d-u=d := by ring
  rwa [he] at hh

theorem unique_AP_coatom {A P Q : Finset ℤ} {m : ℕ}
    (hm : 4≤m) (hA : A.card=m+1) (hbad : ¬IsAP A)
    (hPA : P⊆A) (hQA : Q⊆A) (hPc : P.card=m) (hQc : Q.card=m)
    (hP : IsAP P) (hQ : IsAP Q) : P=Q := by
  by_contra hne
  have hPM : (P\Q).card≤1 := by
    have hsub : P\Q⊆A\Q := by
      intro x hx
      exact Finset.mem_sdiff.mpr ⟨hPA (Finset.mem_sdiff.mp hx).1,(Finset.mem_sdiff.mp hx).2⟩
    have hc := Finset.card_sdiff_add_card_eq_card hQA
    have hl := Finset.card_le_card hsub
    omega
  have hQM : (Q\P).card≤1 := by
    have hsub : Q\P⊆A\P := by
      intro x hx
      exact Finset.mem_sdiff.mpr ⟨hQA (Finset.mem_sdiff.mp hx).1,(Finset.mem_sdiff.mp hx).2⟩
    have hc := Finset.card_sdiff_add_card_eq_card hPA
    have hl := Finset.card_le_card hsub
    omega
  obtain ⟨d,p,hPd,_hp⟩ := (isAP_iff_exists_APAt P).mp hP
  obtain ⟨e,q,hQe,_hq⟩ := (isAP_iff_exists_APAt Q).mp hQ
  have hde : d=e := le_antisymm
    (Int.le_of_dvd hQe.1 (step_divides hQe hPd (by omega) hQM))
    (Int.le_of_dvd hPd.1 (step_divides hPd hQe (by omega) hPM))
  subst e
  obtain ⟨u,hu,_hu1⟩ := retained_adjacent hPd (by omega : 4≤P.card) hPM
  have huP := (Finset.mem_inter.mp hu).1
  have huQ := (Finset.mem_inter.mp hu).2
  have hU : IsAP (P∪Q) := by
    apply (isAP_iff_exists_APAt (P∪Q)).mpr
    refine ⟨d,u,?_,Finset.mem_union.mpr (Or.inl huP)⟩
    change PrivateUnion.APAt d u (fun x => x∈P∪Q)
    simpa only [Finset.mem_union] using
      (PrivateUnion.union_APAt d u (fun x => x∈P) (fun x => x∈Q)
        (apAt_rebase hPd huP) (apAt_rebase hQe huQ) huP huQ)
  have hUeq : P∪Q=A := by
    apply Finset.eq_of_subset_of_card_le (Finset.union_subset hPA hQA)
    by_contra hn
    have hUc : (P∪Q).card≤m := by omega
    have hPU : P=P∪Q := Finset.eq_of_subset_of_card_le Finset.subset_union_left (by omega)
    have hQP : Q⊆P := by rw [hPU]; exact Finset.subset_union_right
    have heq : Q=P := Finset.eq_of_subset_of_card_le hQP (by omega)
    exact hne heq.symm
  exact hbad (hUeq ▸ hU)

#print axioms missing_force
#print axioms retained_adjacent
#print axioms step_divides
#print axioms unique_AP_coatom
end
end JSP233.APCoatom65172
