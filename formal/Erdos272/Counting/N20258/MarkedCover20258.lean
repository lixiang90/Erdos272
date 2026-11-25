module

public import Erdos272.Geometry.N20258.CoreWitnessSweep20258

@[expose] public section
namespace JSP233.MarkedCover20258
open StarCompletion APGeometry APCount41 CoreWitnessSweep20258
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false

private theorem card_cover {α β : Type*} [DecidableEq α] [DecidableEq β]
    {G : Finset α} {I : Finset β} {f : β → Finset α} {v : ℕ}
    (hit : ∀ S∈G,∃ i∈I,S∈f i) (each : ∀ i∈I,(f i).card≤v) : G.card≤I.card*v := by
  have sub : G⊆I.biUnion f := fun S hs => Finset.mem_biUnion.mpr (hit S hs)
  have sum := Finset.sum_le_sum each
  exact (Finset.card_le_card sub).trans (Finset.card_biUnion_le.trans (by simpa using sum))

private theorem weight_cover {α β : Type*} [DecidableEq α] [DecidableEq β]
    {G A : Finset α} {I : Finset β} {f : α → Finset β} (w : α → ℕ) {v : ℕ}
    (sub : G⊆A) (hit : ∀ S∈G,(f S∩I).Nonempty)
    (each : ∀ i∈I,∑ S∈A.filter (fun S => i∈f S),w S≤v) : ∑ S∈G,w S≤I.card*v := by
  calc
    _ ≤ ∑ S∈G,∑ i∈I,if i∈f S then w S else 0 := by
      apply Finset.sum_le_sum
      intro S hs
      obtain ⟨i,hi⟩ := hit S hs
      obtain ⟨inside,allowed⟩ := Finset.mem_inter.mp hi
      simpa only [ite_eq_left inside] using Finset.single_le_sum
        (f:=fun i => if i∈f S then w S else 0) (fun _ _ => Nat.zero_le _) allowed
    _ = ∑ i∈I,∑ S∈G.filter (fun S => i∈f S),w S := by
      rw [Finset.sum_comm]; simp only [Finset.sum_filter]
    _ ≤ ∑ _i∈I,v := Finset.sum_le_sum (fun i hi =>
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset_filter _ sub)
        (fun _ _ _ => Nat.zero_le _)).trans (each i hi))
    _ = _ := by simp

private def points (P : Finset ℤ → Finset ℤ) (T : Finset ℤ) : Finset ℤ :=
  insert (High (P T)) (T\P T)

private theorem disjoint_member {P : Finset ℤ → Finset ℤ} {S T : Finset ℤ}
    (cores : Disjoint (P T) (P S)) (marks : ¬(P S∩points P T).Nonempty) : Disjoint (P S) T := by
  apply Finset.disjoint_left.mpr
  intro x hS hT
  by_cases inside : x∈P T
  · exact Finset.disjoint_left.mp cores inside hS
  · exact marks ⟨x,Finset.mem_inter.mpr ⟨hS,Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr ⟨hT,inside⟩)⟩⟩

/-- Sum all exterior incidences of a fixed stride. The first witness uses
unrestricted exterior marks. Every later witness can use a mark in that
first member, or else force a repeated exterior mark by disjointness. -/
theorem weight {A : Finset (Finset ℤ)} {P : Finset ℤ → Finset ℤ} {d : ℤ}
    {k s cost o u : ℕ} (cores : ∀ S∈A,(P S).Nonempty) (step : ∀ S∈A,∃ p,APAt d p (P S))
    (meets : ∀ S∈A,∀ T∈A,(S∩T).Nonempty)
    (few : ∀ S∈A,(S\P S).card≤k) (size : ∀ S∈A,S.card≤s)
    (pivot : ∀ t,∑ S∈A.filter (fun S => t∈P S),(S\P S).card≤cost)
    (pair : ∀ t x,((A.filter (fun S => t∈P S)).filter (fun S => x∈S\P S)).card≤o)
    (outer : ∀ x,(A.filter (fun S => x∈S\P S)).card≤u) :
    ∑ S∈A,(S\P S).card≤(k+1)*cost+k*min (s*u) (k*(k+1)*(s*o+u)) := by
  rcases A.eq_empty_or_nonempty with rfl|nonempty
  · simp
  obtain ⟨V,hV,skip⟩ := first nonempty cores step
  let R := A.filter (fun S => ¬(P S∩points P V).Nonempty)
  have ra : R⊆A := Finset.filter_subset _ _
  have missV (S : Finset ℤ) (hs : S∈R) : Disjoint (P V) (P S) := by
    apply skip S (ra hs)
    exact fun hit => (Finset.mem_filter.mp hs).2 ⟨_,Finset.mem_inter.mpr ⟨hit,Finset.mem_insert_self _ _⟩⟩
  have avoidsV (S : Finset ℤ) (hs : S∈R) : Disjoint (P S) V :=
    disjoint_member (missV S hs) (Finset.mem_filter.mp hs).2
  have known (S : Finset ℤ) (hs : S∈R) : ∃ x∈V,x∈S\P S := by
    obtain ⟨x,hx⟩ := meets S (ra hs) V hV
    obtain ⟨xs,xv⟩ := Finset.mem_inter.mp hx
    exact ⟨x,xv,Finset.mem_sdiff.mpr ⟨xs,fun hp => Finset.disjoint_left.mp (avoidsV S hs) hp xv⟩⟩
  have firstBound : R.card≤s*u := by
    apply le_trans (card_cover (I:=V) (f:=fun x => A.filter (fun S => x∈S\P S)) ?_ (fun x _ => outer x))
      (Nat.mul_le_mul_right _ (size V hV))
    intro S hs
    obtain ⟨x,xv,ex⟩ := known S hs
    exact ⟨x,xv,Finset.mem_filter.mpr ⟨ra hs,ex⟩⟩
  obtain ⟨W,wr,wk,wd,complete⟩ := select k R (fun S hs => cores S (ra hs)) (fun S hs => step S (ra hs))
  let J := W.biUnion (points P)
  let Z := (insert V W).biUnion (fun S => S\P S)
  have pointsSize (T : Finset ℤ) (ht : T∈A) : (points P T).card≤k+1 :=
    (Finset.card_insert_le _ _).trans (Nat.add_le_add_right (few T ht) _)
  have jSize : J.card≤k*(k+1) := by
    have sum := Finset.sum_le_sum (s:=W) (fun T ht => pointsSize T (ra (wr ht)))
    exact Finset.card_biUnion_le.trans ((by simpa using sum : (∑ T∈W,(points P T).card)≤W.card*(k+1)).trans
      (Nat.mul_le_mul_right _ wk))
  have allSub : insert V W ⊆ A := Finset.insert_subset hV (wr.trans ra)
  have zSize : Z.card≤k*(k+1) := by
    have sum := Finset.sum_le_sum (s:=insert V W) (fun T ht => few T (allSub ht))
    have sc := (Finset.card_insert_le V W).trans (Nat.add_le_add_right wk 1)
    exact Finset.card_biUnion_le.trans ((by simpa using sum :
      (∑ T∈insert V W,(T\P T).card)≤(insert V W).card*k).trans (by simpa [Nat.mul_comm k] using Nat.mul_le_mul_right k sc))
  let B := R.filter (fun S => (P S∩J).Nonempty)
  let C := R.filter (fun S => ¬(P S∩J).Nonempty)
  have br : B⊆R := Finset.filter_subset _ _
  have cr : C⊆R := Finset.filter_subset _ _
  have countB : B.card≤k*(k+1)*(s*o) := by
    apply (card_cover (I:=J) (f:=fun t => R.filter (fun S => t∈P S)) ?_ ?_).trans (Nat.mul_le_mul_right _ jSize)
    · intro S hs
      obtain ⟨t,ht⟩ := (Finset.mem_filter.mp hs).2
      obtain ⟨tp,tj⟩ := Finset.mem_inter.mp ht
      exact ⟨t,tj,Finset.mem_filter.mpr ⟨br hs,tp⟩⟩
    · intro t _
      apply (card_cover (I:=V) (f:=fun x => (A.filter (fun S => t∈P S)).filter (fun S => x∈S\P S))
        ?_ (fun x _ => pair t x)).trans (Nat.mul_le_mul_right _ (size V hV))
      intro S hs
      obtain ⟨sr,hit⟩ := Finset.mem_filter.mp hs
      obtain ⟨x,xv,ex⟩ := known S sr
      exact ⟨x,xv,Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨ra sr,hit⟩,ex⟩⟩
  have unionDis : ((insert V W : Finset _) : Set (Finset ℤ)).PairwiseDisjoint P := by
    rw [Finset.coe_insert]
    exact wd.insert (fun T ht _ => missV T (wr ht))
  have countC : C.card≤k*(k+1)*u := by
    apply (card_cover (I:=Z) (f:=fun x => A.filter (fun S => x∈S\P S)) ?_ (fun x _ => outer x)).trans
      (Nat.mul_le_mul_right _ zSize)
    intro S hs
    have sa := ra (cr hs)
    have misses (T : Finset ℤ) (ht : T∈W) : ¬(P S∩points P T).Nonempty := by
      rintro ⟨z,hz⟩
      obtain ⟨hsz,htz⟩ := Finset.mem_inter.mp hz
      exact (Finset.mem_filter.mp hs).2 ⟨z,Finset.mem_inter.mpr ⟨hsz,Finset.mem_biUnion.mpr ⟨T,ht,htz⟩⟩⟩
    obtain ⟨full,dis⟩ := complete S (cr hs) (fun T ht h => misses T ht
      ⟨_,Finset.mem_inter.mpr ⟨h,Finset.mem_insert_self _ _⟩⟩)
    have vout : V∉W := fun h => (Finset.mem_filter.mp (wr h)).2
      ⟨_,Finset.mem_inter.mpr ⟨(high_spec (cores V hV)).1,Finset.mem_insert_self _ _⟩⟩
    obtain ⟨T,ht,x,ex,z⟩ := repeat_mark unionDis
      (by rw [Finset.card_insert_of_notMem vout,full]; exact Nat.lt_succ_of_le (few S sa))
      (fun T ht => meets S sa T (allSub ht)) (fun T ht => by
        rcases Finset.mem_insert.mp ht with rfl|ht
        · exact avoidsV S (cr hs)
        · exact disjoint_member (dis T ht) (misses T ht))
    exact ⟨x,Finset.mem_biUnion.mpr ⟨T,ht,z⟩,Finset.mem_filter.mpr ⟨sa,ex⟩⟩
  have rest := Finset.card_filter_add_card_filter_not (s:=R) (fun S => (P S∩J).Nonempty)
  change B.card+C.card=R.card at rest
  have rc : R.card≤min (s*u) (k*(k+1)*(s*o+u)) := by
    apply le_min firstBound
    rw [←rest,Nat.mul_add]
    exact Nat.add_le_add countB countC
  let H := A.filter (fun S => (P S∩points P V).Nonempty)
  have head : ∑ S∈H,(S\P S).card≤(k+1)*cost :=
    (weight_cover (I:=points P V) (fun S => (S\P S).card) (Finset.filter_subset _ _)
      (fun S hs => (Finset.mem_filter.mp hs).2) (fun t _ => pivot t)).trans (Nat.mul_le_mul_right _ (pointsSize V hV))
  have tail : ∑ S∈R,(S\P S).card≤k*min (s*u) (k*(k+1)*(s*o+u)) := by
    have v := Finset.sum_le_sum (s:=R) (fun S hs => few S (ra hs))
    exact (by simpa [Nat.mul_comm k] using v : ∑ S∈R,(S\P S).card≤k*R.card).trans (Nat.mul_le_mul_left k rc)
  rw [← Finset.sum_filter_add_sum_filter_not A (fun S => (P S∩points P V).Nonempty) (fun S => (S\P S).card)]
  exact Nat.add_le_add head tail

#print axioms weight
end
end JSP233.MarkedCover20258
