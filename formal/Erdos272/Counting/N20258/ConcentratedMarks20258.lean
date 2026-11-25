module

public import Erdos272.Geometry.N20258.ConcentratedCores20258

@[expose] public section
namespace JSP233.ConcentratedMarks20258
open StarCompletion APGeometry APCount41 MarkedPairCount20258
open scoped Classical BigOperators
set_option autoImplicit false

/-- In a family of bounded core depth, orient pairs of intersecting cores by
their right endpoints. A remaining meeting uses an exterior point of at
least one member. Exterior/exterior pairs need only one charge. -/
theorem sparse {A : Finset (Finset ℤ)} {P : Finset ℤ → Finset ℤ} {d : ℤ} {k D u : ℕ}
    (nonempty : ∀ S∈A,(P S).Nonempty) (step : ∀ S∈A,∃ p,APAt d p (P S))
    (meet : ∀ S∈A,∀ T∈A,(S∩T).Nonempty) (few : ∀ S∈A,(S\P S).card≤k)
    (depth : ∀ t,(A.filter (fun S => t∈P S)).card≤D)
    (outer : ∀ x,(A.filter (fun S => x∈S\P S)).card≤u) :
    A.card≤2*(k+1)*D+k*u := by
  classical
  let ext (S : Finset ℤ) := S\P S
  let sites (S : Finset ℤ) := insert (High (P S)) (ext S)
  let rel (S T : Finset ℤ) := (sites S∩P T).Nonempty
  let extra (S T : Finset ℤ) := (ext S∩ext T).Nonempty
  have edges (S : Finset ℤ) (hs : S∈A) : (A.filter (rel S)).card≤(k+1)*D := by
    have sz : (sites S).card≤k+1 := (Finset.card_insert_le ..).trans (Nat.add_le_add_right (few S hs) 1)
    exact (hits A (sites S) P (fun t _ => depth t)).trans (Nat.mul_le_mul_right D sz)
  have doubles (S : Finset ℤ) (hs : S∈A) : (A.filter (extra S)).card≤k*u :=
    (hits A (ext S) ext (fun x _ => outer x)).trans (Nat.mul_le_mul_right u (few S hs))
  have direction (S T : Finset ℤ) (hs : S∈A) (ht : T∈A) (cores : (P S∩P T).Nonempty)
      (le : High (P S)≤High (P T)) : rel S T := by
    obtain ⟨p,ap⟩ := step S hs
    obtain ⟨q,aq⟩ := step T ht
    exact ⟨_,Finset.mem_inter.mpr ⟨Finset.mem_insert_self ..,
      CoreCleanup208.same_step_intersection_high ap aq (nonempty S hs) (nonempty T ht) le cores⟩⟩
  have count := rectangle A A (fun S T => rel S T ∨ extra S T) rel
    (l:=(k+1)*D+k*u) (r:=(k+1)*D) (by
      intro S hs T ht
      obtain ⟨x,hx⟩ := meet S hs T ht
      obtain ⟨xs,xt⟩ := Finset.mem_inter.mp hx
      by_cases a : x∈P S <;> by_cases b : x∈P T
      · rcases le_total (High (P S)) (High (P T)) with le|le
        · exact Or.inl (Or.inl (direction S T hs ht ⟨x,Finset.mem_inter.mpr ⟨a,b⟩⟩ le))
        · exact Or.inr (direction T S ht hs ⟨x,Finset.mem_inter.mpr ⟨b,a⟩⟩ le)
      · exact Or.inr ⟨x,Finset.mem_inter.mpr ⟨Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr ⟨xt,b⟩),a⟩⟩
      · exact Or.inl (Or.inl ⟨x,Finset.mem_inter.mpr ⟨Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr ⟨xs,a⟩),b⟩⟩)
      · exact Or.inl (Or.inr ⟨x,Finset.mem_inter.mpr ⟨Finset.mem_sdiff.mpr ⟨xs,a⟩,Finset.mem_sdiff.mpr ⟨xt,b⟩⟩⟩))
    (by
      intro S hs
      rw [Finset.filter_or]
      exact (Finset.card_union_le ..).trans (Nat.add_le_add (edges S hs) (doubles S hs))) edges
  rcases A.eq_empty_or_nonempty with empty|ne
  · simp [empty]
  apply Nat.le_of_mul_le_mul_left (a:=A.card)
  · calc
      _ ≤ _ := count
      _ = _ := by ring
  · exact Finset.card_pos.mpr ne

/-- The concentrated part pays its actual exterior incidences at a single
pivot. The remainder pays at most k incidences for each surviving member. -/
theorem weight {A : Finset (Finset ℤ)} {P : Finset ℤ → Finset ℤ} {d : ℤ} {k s o u cost : ℕ}
    (nonempty : ∀ S∈A,(P S).Nonempty) (step : ∀ S∈A,∃ p,APAt d p (P S))
    (meet : ∀ S∈A,∀ T∈A,(S∩T).Nonempty) (few : ∀ S∈A,(S\P S).card≤k)
    (size : ∀ S∈A,S.card≤s) (pivot : ∀ t,∑ S∈A.filter (fun S => t∈P S),(S\P S).card≤cost)
    (pair : ∀ t x,((A.filter (fun S => t∈P S)).filter (fun S => x∈S\P S)).card≤o)
    (outer : ∀ x,(A.filter (fun S => x∈S\P S)).card≤u) :
    ∑ S∈A,(S\P S).card≤cost+k*(2*(k+1)*(2*s*o)+k*u) := by
  classical
  obtain ⟨t,depth⟩ := ConcentratedCores20258.pivot step meet size pair
  let R := A.filter (fun S => t∉P S)
  have sub : R⊆A := Finset.filter_subset _ _
  have tail := sparse (A:=R) (fun S hs => nonempty S (sub hs)) (fun S hs => step S (sub hs))
    (fun S hs T ht => meet S (sub hs) T (sub ht)) (fun S hs => few S (sub hs)) depth
    (fun x => (Finset.card_le_card (Finset.filter_subset_filter _ sub)).trans (outer x))
  have paid : ∑ S∈R,(S\P S).card≤k*R.card := by
    simpa [Nat.mul_comm] using Finset.sum_le_sum (s:=R) (fun S hs => few S (sub hs))
  rw [←Finset.sum_filter_add_sum_filter_not A (fun S => t∈P S) (fun S => (S\P S).card)]
  exact Nat.add_le_add (pivot t) (paid.trans (Nat.mul_le_mul_left k tail))

#print axioms sparse
#print axioms weight
end JSP233.ConcentratedMarks20258
