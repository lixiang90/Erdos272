module

public import Erdos272.Core.N65172.APCoatom65172
public import Erdos272.Counting.N20258.TwoTransversals20258

@[expose] public section
namespace JSP233.CoatomLayer20258
open StarCompletion PrivatePairExistence
open scoped Classical
noncomputable section
set_option autoImplicit false

/-- At a fixed site, a member of a uniform crooked layer has a private
second site whenever its only possible nonsingleton intersections with
other members of the layer are AP coatoms. -/
theorem private_site {N m : ℕ} {A : Finset (Finset ℤ)} (hm : 5 ≤ m)
    (legal : Legal (Ground N) A) (bad : ∀ S ∈ A, ¬IsAP S) (size : ∀ S ∈ A, S.card=m)
    (shape : ∀ S ∈ A, ∀ T ∈ A, S ≠ T → 2 ≤ (S ∩ T).card → (S ∩ T).card=m-1)
    {S : Finset ℤ} (hS : S ∈ A) {x : ℤ} (hx : x ∈ S) :
    ∃ y ∈ S, x ≠ y ∧ ∀ T ∈ A, x ∈ T → y ∈ T → T=S := by
  have two {T : Finset ℤ} {y : ℤ} (hy : y ∈ S) (ne : x ≠ y) (xt : x ∈ T) (yt : y ∈ T) :
      2 ≤ (S ∩ T).card := Finset.one_lt_card.mpr
    ⟨x,Finset.mem_inter.mpr ⟨hx,xt⟩,y,Finset.mem_inter.mpr ⟨hy,yt⟩,ne⟩
  by_cases hit : ∃ T ∈ A, S ≠ T ∧ x ∈ T ∧ 2 ≤ (S ∩ T).card
  · obtain ⟨T,hT,st,xt,st2⟩ := hit
    have card := shape S hS T hT st st2
    have proper : ¬S ⊆ S ∩ T := by
      intro sub
      have := Finset.card_le_card sub
      have := size S hS
      omega
    obtain ⟨y,hy,miss⟩ := Finset.not_subset.mp proper
    have xy : x ≠ y := by rintro rfl; exact miss (Finset.mem_inter.mpr ⟨hx,xt⟩)
    refine ⟨y,hy,xy,?_⟩
    intro V hV xv yv
    by_contra vs
    have cv := shape S hS V hV (Ne.symm vs) (two hy xy xv yv)
    have same := APCoatom65172.unique_AP_coatom (m := m-1) (by omega)
      (show S.card=m-1+1 by have := size S hS; omega) (bad S hS)
      (Finset.inter_subset_left : S ∩ T ⊆ S) (Finset.inter_subset_left : S ∩ V ⊆ S)
      card cv (legal.2 S hS T hT st) (legal.2 S hS V hV (Ne.symm vs))
    exact miss (same ▸ Finset.mem_inter.mpr ⟨hy,yv⟩)
  · have distinct : (S.erase x).Nonempty := by
      apply Finset.card_pos.mp
      rw [Finset.card_erase_of_mem hx,size S hS]
      omega
    obtain ⟨y,hy⟩ := distinct
    obtain ⟨neq,ys⟩ := Finset.mem_erase.mp hy
    exact ⟨y,ys,Ne.symm neq,fun T hT xt yt => by
      by_contra ts
      exact hit ⟨T,hT,Ne.symm ts,xt,two ys (Ne.symm neq) xt yt⟩⟩

/-- A transversal of a uniform layer with only singleton and coatom
intersections covers it with at most one member per ordered pair of sites. -/
theorem layer_count {N m : ℕ} {A : Finset (Finset ℤ)} {P : Finset ℤ} (hm : 5 ≤ m)
    (legal : Legal (Ground N) A) (bad : ∀ S ∈ A, ¬IsAP S) (size : ∀ S ∈ A, S.card=m)
    (shape : ∀ S ∈ A, ∀ T ∈ A, S ≠ T → 2 ≤ (S ∩ T).card → (S ∩ T).card=m-1)
    (hit : ∀ S ∈ A, (P ∩ S).Nonempty) : A.card ≤ P.card*N := by
  have code (S : Finset ℤ) (hs : S ∈ A) : ∃ p ∈ P.product (Ground N),
      p.1 ∈ S ∧ p.2 ∈ S ∧ ∀ T ∈ A, p.1 ∈ T → p.2 ∈ T → T=S := by
    obtain ⟨x,hx⟩ := hit S hs
    obtain ⟨xp,xs⟩ := Finset.mem_inter.mp hx
    obtain ⟨y,ys,_,priv⟩ := private_site hm legal bad size shape hs xs
    exact ⟨(x,y),Finset.mem_product.mpr ⟨xp,legal.1 S hs ys⟩,xs,ys,priv⟩
  let f (S : Finset ℤ) : ℤ × ℤ := if hs : S ∈ A then Classical.choose (code S hs) else (0,0)
  have hf (S : Finset ℤ) (hs : S ∈ A) : f S ∈ P.product (Ground N) ∧
      (f S).1 ∈ S ∧ (f S).2 ∈ S ∧ ∀ T ∈ A, (f S).1 ∈ T → (f S).2 ∈ T → T=S := by
    simpa only [f,dif_pos hs] using Classical.choose_spec (code S hs)
  have bound := Finset.card_le_card_of_injOn f (fun S hS => (hf S hS).1) (fun S hS T hT eqn =>
    (hf T hT).2.2.2 S hS (eqn ▸ (hf S hS).2.1) (eqn ▸ (hf S hS).2.2.1))
  exact bound.trans_eq ((Finset.card_product P (Ground N)).trans (by rw [ground_card]))

/-- Across all uniform layers the same dichotomy either bounds the whole
crooked family or bounds the number of members at the cutoff itself. -/
theorem actual {N m : ℕ} {F : Finset (Finset ℤ)} (hm : 5 ≤ m) (ground : m+1 ≤ N)
    (legal : Legal (Ground N) F)
    (omits : ∀ x ∈ Ground N, ∃ Q ∈ CrookedMembers F, x ∉ Q ∧ Q.card ≤ m) :
    (CrookedMembers F).card ≤ ((m-2)*m+4)*(N-2) ∨
      ((CrookedMembers F).filter (fun S => S.card=m)).card ≤ m*N := by
  let A := (CrookedMembers F).filter fun S => S.card=m
  have sub : A ⊆ CrookedMembers F := Finset.filter_subset _ _
  have mem {S : Finset ℤ} (hS : S ∈ A) := (Finset.mem_filter.mp (sub hS)).1
  have size (S : Finset ℤ) (hs : S ∈ A) : S.card=m := (Finset.mem_filter.mp hs).2
  by_cases middle : ∃ S ∈ A, ∃ T ∈ A, 2 ≤ (S ∩ T).card ∧ (S ∩ T).card ≤ m-2
  · left
    obtain ⟨S,hS,T,hT,lo,hi⟩ := middle
    have hp := TwoTransversals20258.actual_two (by omega) ground legal (mem hS)
      (Finset.card_pos.mp (by rw [size S hS]; omega)) (mem hT)
      (Finset.card_pos.mp (by rw [size T hT]; omega)) omits
    let i := (S ∩ T).card
    have a := Finset.card_sdiff_add_card_inter S T
    have b := Finset.card_sdiff_add_card_inter T S
    rw [Finset.inter_comm T S] at b
    have rs := size S hS
    have rt := size T hT
    change (S ∩ T).card ≥ 2 at lo
    have ds : (S \ T).card=m-i := by dsimp only [i]; omega
    have dt : (T \ S).card=m-i := by dsimp only [i]; omega
    have cut : i*m+(m-i)*(m-i) ≤ (m-2)*m+4 := by
      have ilo : 2 ≤ i := lo
      have iup : i+2 ≤ m := by dsimp only [i]; omega
      have prod := mul_nonneg (show (0 : ℤ) ≤ (i : ℤ)-2 by omega)
        (show (0 : ℤ) ≤ (m : ℤ)-(i : ℤ)-2 by omega)
      zify [show i ≤ m by omega, show 2 ≤ m by omega]
      nlinarith only [prod]
    rw [ds,dt] at hp
    have root := Nat.mul_le_mul_left i (Nat.sub_le (m*(N-2)) (m.choose 2))
    calc
      _ ≤ i*(m*(N-2))+(m-i)*(m-i)*(N-2) := hp.trans (Nat.add_le_add_right root _)
      _ = (i*m+(m-i)*(m-i))*(N-2) := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ cut
  · right
    by_cases ne : A.Nonempty
    · obtain ⟨P,hP⟩ := ne
      have geometry : Legal (Ground N) A :=
        ⟨fun S hs => legal.1 S (mem hs), fun S hs T ht => legal.2 S (mem hs) T (mem ht)⟩
      have shapes (S : Finset ℤ) (hs : S ∈ A) (T : Finset ℤ) (ht : T ∈ A) (st : S ≠ T)
          (two : 2 ≤ (S ∩ T).card) : (S ∩ T).card=m-1 := by
        have lt : (S ∩ T).card < m := by
          by_contra! ge
          have eqS := Finset.eq_of_subset_of_card_le (Finset.inter_subset_left : S ∩ T ⊆ S) ((size S hs).le.trans ge)
          have eqT := Finset.eq_of_subset_of_card_le (Finset.inter_subset_right : S ∩ T ⊆ T) ((size T ht).le.trans ge)
          exact st (eqS.symm.trans eqT)
        have notLow : ¬ (S ∩ T).card ≤ m-2 := fun h => middle ⟨S,hs,T,ht,two,h⟩
        omega
      have hit (S : Finset ℤ) (hs : S ∈ A) : (P ∩ S).Nonempty := by
        by_cases eqn : P=S
        · simpa [eqn] using (Finset.card_pos.mp (by rw [size S hs]; omega) : S.Nonempty)
        · exact isAP_nonempty (legal.2 P (mem hP) S (mem hs) eqn)
      simpa only [size P hP] using layer_count hm geometry (fun _ hs => (Finset.mem_filter.mp (sub hs)).2) size shapes hit
    · change A.card ≤ m*N
      simp [Finset.not_nonempty_iff_eq_empty.mp ne]

#print axioms actual
end
end JSP233.CoatomLayer20258
