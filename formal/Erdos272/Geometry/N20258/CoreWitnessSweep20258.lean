module

public import Erdos272.Resources.CoreCleanup208

@[expose] public section
namespace JSP233.CoreWitnessSweep20258
open StarCompletion APGeometry APCount41
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false

/-- On a fixed stride choose the core with smallest right endpoint. Every
core that misses this endpoint misses the whole chosen core. -/
theorem first {A : Finset (Finset ℤ)} {P : Finset ℤ → Finset ℤ} {d : ℤ}
    (nonempty : A.Nonempty) (cores : ∀ S∈A,(P S).Nonempty)
    (step : ∀ S∈A,∃ p,APAt d p (P S)) :
    ∃ W∈A,∀ S∈A,High (P W)∉P S → Disjoint (P W) (P S) := by
  obtain ⟨W,hw,least⟩ := Finset.exists_min_image A (fun S => High (P S)) nonempty
  refine ⟨W,hw,?_⟩
  intro S hs miss
  obtain ⟨p,hp⟩ := step W hw
  obtain ⟨q,hq⟩ := step S hs
  exact Finset.disjoint_left.mpr fun x hx hy =>
    miss (CoreCleanup208.same_step_intersection_high hp hq (cores W hw) (cores S hs)
      (least S hs) ⟨x,Finset.mem_inter.mpr ⟨hx,hy⟩⟩)

/-- Greedily take at most k disjoint cores. If a core avoids every chosen
right endpoint, all k witnesses exist and each is disjoint from that core. -/
theorem select {P : Finset ℤ → Finset ℤ} {d : ℤ} (k : ℕ) (A : Finset (Finset ℤ))
    (cores : ∀ S∈A,(P S).Nonempty) (step : ∀ S∈A,∃ p,APAt d p (P S)) :
    ∃ W⊆A,W.card≤k ∧ (W : Set (Finset ℤ)).PairwiseDisjoint P ∧
      ∀ S∈A,(∀ T∈W,High (P T)∉P S) → W.card=k ∧ ∀ T∈W,Disjoint (P T) (P S) := by
  induction k generalizing A with
  | zero =>
    exact ⟨∅,Finset.empty_subset _,by simp,by simp,by simp⟩
  | succ k ih =>
    rcases A.eq_empty_or_nonempty with rfl|ne
    · exact ⟨∅,by simp,by simp,by simp,by simp⟩
    obtain ⟨V,hv,skip⟩ := first ne cores step
    let R := A.filter (fun S => High (P V)∉P S)
    have sub : R⊆A := Finset.filter_subset _ _
    obtain ⟨W,wr,wk,wd,survivor⟩ := ih R (fun S hs => cores S (sub hs)) (fun S hs => step S (sub hs))
    have away (S : Finset ℤ) (hs : S∈R) := skip S (sub hs) (Finset.mem_filter.mp hs).2
    have vout : V∉W := fun mem => (Finset.mem_filter.mp (wr mem)).2 (high_spec (cores V hv)).1
    refine ⟨insert V W,Finset.insert_subset hv (wr.trans sub),?_,?_,?_⟩
    · rw [Finset.card_insert_of_notMem vout]; omega
    · rw [Finset.coe_insert]
      exact wd.insert (fun T ht _ => away T (wr ht))
    · intro S hs avoids
      have r : S∈R := Finset.mem_filter.mpr ⟨hs,avoids V (Finset.mem_insert_self _ _)⟩
      obtain ⟨full,rest⟩ := survivor S r (fun T ht => avoids T (Finset.mem_insert_of_mem ht))
      refine ⟨by rw [Finset.card_insert_of_notMem vout,full],?_⟩
      intro T ht
      rcases Finset.mem_insert.mp ht with rfl|ht
      · exact away S r
      · exact rest T ht

/-- A member that meets more disjoint-core witnesses than it has exterior
points must share an exterior point with a witness if its core avoids them all. -/
theorem repeat_mark {W : Finset (Finset ℤ)} {P : Finset ℤ → Finset ℤ} {S : Finset ℤ}
    (separate : (W : Set (Finset ℤ)).PairwiseDisjoint P)
    (many : (S\P S).card<W.card) (meets : ∀ T∈W,(S∩T).Nonempty)
    (avoids : ∀ T∈W,Disjoint (P S) T) :
    ∃ T∈W,∃ x∈S\P S,x∈T\P T := by
  by_contra! no
  have pick (T : Finset ℤ) (ht : T∈W) : ∃ x∈S\P S,x∈P T := by
    obtain ⟨x,hx⟩ := meets T ht
    obtain ⟨xs,xt⟩ := Finset.mem_inter.mp hx
    have ext : x∈S\P S := Finset.mem_sdiff.mpr ⟨xs,fun h => Finset.disjoint_left.mp (avoids T ht) h xt⟩
    exact ⟨x,ext,by by_contra miss; exact no T ht x ext (Finset.mem_sdiff.mpr ⟨xt,miss⟩)⟩
  let f (T : Finset ℤ) := if ht : T∈W then Classical.choose (pick T ht) else 0
  have chosen (T : Finset ℤ) (ht : T∈W) : f T∈S\P S ∧ f T∈P T := by
    simpa only [f,dite_eq_left ht] using Classical.choose_spec (pick T ht)
  apply (Nat.not_le_of_lt many)
  apply Finset.card_le_card_of_injOn f (fun T ht => (chosen T ht).1)
  intro T ht V hv eqn
  by_contra diff
  exact Finset.disjoint_left.mp (separate ht hv diff) (chosen T ht).2 (eqn ▸ (chosen V hv).2)

#print axioms select
#print axioms repeat_mark
end
end JSP233.CoreWitnessSweep20258
