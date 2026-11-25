module

public import Erdos272.Geometry.N20258.SharedOutside20258
public import Erdos272.Resources.ResidualOccupancy208

@[expose] public section
namespace JSP233.MarkedCoreEnds20258
open StarCompletion APGeometry
set_option autoImplicit false

/-- A core interval avoiding the largest left endpoint misses the entire
corresponding core. Its own exterior mark must meet that member. -/
private theorem left_end {a b t l h q : ℤ} (left : a≤l)
    (meet : (insert t (Finset.Icc a b) ∩ insert q (Finset.Icc l h)).Nonempty) :
    l∈Finset.Icc a b ∨ q∈Finset.Icc a b ∨ t∈insert q (Finset.Icc l h) := by
  obtain ⟨z,hz⟩ := meet
  obtain ⟨inside,other⟩ := Finset.mem_inter.mp hz
  simp only [Finset.mem_insert,Finset.mem_Icc] at inside other ⊢
  omega

/-- Use the member with largest left endpoint l and the member with smallest
right endpoint r. In the last case only their two exterior marks are possible. -/
theorem classify {a b t l h q w r p : ℤ} (left : a≤l) (right : r≤b) (gap : r<l)
    (meetQ : (insert t (Finset.Icc a b) ∩ insert q (Finset.Icc l h)).Nonempty)
    (meetP : (insert t (Finset.Icc a b) ∩ insert p (Finset.Icc w r)).Nonempty) :
    l∈Finset.Icc a b ∨ q∈Finset.Icc a b ∨
      (t∈insert q (Finset.Icc l h) ∧ (r∈Finset.Icc a b ∨ p∈Finset.Icc a b)) ∨ t=p ∨ t=q := by
  rcases left_end left meetQ with hit|hit|tip
  · exact Or.inl hit
  · exact Or.inr (Or.inl hit)
  obtain ⟨z,hz⟩ := meetP
  obtain ⟨inside,other⟩ := Finset.mem_inter.mp hz
  simp only [Finset.mem_insert,Finset.mem_Icc] at inside other tip ⊢
  omega

/-- For a fixed stride and exterior point, deleting the two endpoints of
each core leaves pairwise disjoint sets of actual lattice sites. -/
theorem disjoint_middle {Ω P Q : Finset ℤ} {F : Finset (Finset ℤ)} {d p x z : ℤ}
    (legal : Legal Ω F) (first : insert x P∈F) (second : insert x Q∈F)
    (ne : insert x P≠insert x Q) (core : APAt d p P) (bad : ¬IsAP (insert x P))
    (out : x∉P) (mid : z-d∈P∩Q ∧ z∈P∩Q ∧ z+d∈P∩Q) : False := by
  let T := insert x Q
  have sub : P∩Q⊆P∩T := Finset.inter_subset_inter_left (Finset.subset_insert _ _)
  have three : 3≤(P∩T).card := by
    have incl : {z-d,z,z+d}⊆P∩T := by
      intro y hy
      simp only [Finset.mem_insert,Finset.mem_singleton] at hy
      rcases hy with rfl|rfl|rfl
      · exact sub mid.1
      · exact sub mid.2.1
      · exact sub mid.2.2
    have pos := core.1
    have card : ({z-d,z,z+d}:Finset ℤ).card=3 := by
      simp [show z≠z+d by omega,show z-d≠z by omega,show z-d≠z+d by omega]
    exact card ▸ Finset.card_le_card incl
  obtain ⟨e,c,step,_,large,_⟩ := SharedOutside20258.stride legal first second ne core bad out
    (Finset.mem_insert_self _ _) three
  have member (v : ℤ) (hv : v∈P∩Q) : v∈insert x P∩insert x Q := by
    obtain ⟨vp,vq⟩ := Finset.mem_inter.mp hv
    exact Finset.mem_inter.mpr ⟨Finset.mem_insert_of_mem vp,Finset.mem_insert_of_mem vq⟩
  have dvd := apAt_dvd_sub step (member z mid.2.1) (member (z+d) mid.2.2)
  rw [show z+d-z=d by ring] at dvd
  have small := Int.le_of_dvd core.1 dvd
  have pos := core.1
  omega

#print axioms classify
#print axioms disjoint_middle

/-- If two actual members share an exterior mark, their same-stride cores
overlap in at most one more site than the allowed number of missing steps. -/
theorem marked_overlap {Ω S T P Q : Finset ℤ} {F : Finset (Finset ℤ)}
    {d t x : ℤ} {k p : ℕ} (legal : Legal Ω F) (first : S∈F) (second : T∈F)
    (different : S≠T) (core : NearAP36.MaximalAPCore S P) (other : Q⊆T)
    (atP : APAt d t P) (atQ : APAt d t Q) (mark : x∈S\P) (hit : x∈T)
    (few : (S\P).card≤k) (two : 2≤p)
    (proper : ∀ δ : ℤ,0<δ → δ∣d → δ<d → (p:ℤ)*δ≤d)
    (longest : ∀ R : Finset ℤ,IsAP R → R⊆S → R.card≤P.card) :
    (P∩Q).card≤k/(p-1)+1 := by
  by_cases small : (P∩Q).card≤1
  · exact small.trans (Nat.le_add_left 1 _)
  have h := (ResidualSpan208.actual_overlap_bounds legal first second different core other
    atP atQ mark hit (by omega) proper longest).1
  have bound := (Nat.le_div_iff_mul_le (by omega : 0<p-1)).mpr (h.trans few)
  omega

/-- At a shared core pivot the occupancy bound pays all exterior marks at once,
even if different members have different defects. -/
theorem marked_weight {N a k p : ℕ} {F : Finset (Finset ℤ)} {d t : ℤ}
    (legal : Legal (Ground N) F) (two : 2≤p) (P : Finset ℤ → Finset ℤ)
    (core : ∀ S∈F,NearAP36.MaximalAPCore S (P S))
    (stride : ∀ S∈F,APAt d t (P S)) (pivot : ∀ S∈F,t∈P S)
    (large : ∀ S∈F,a+1≤(P S).card) (few : ∀ S∈F,(S\P S).card≤k)
    (longest : ∀ S∈F,∀ R : Finset ℤ,IsAP R → R⊆S → R.card≤(P S).card)
    (proper : ∀ δ : ℤ,0<δ → δ∣d → δ<d → (p:ℤ)*δ≤d) :
    ∑ S∈F,(S\P S).card ≤ N*((if d*(a:ℤ)≤(N:ℤ)-1 then 1 else 0)+
      (if d*(ResidualSpan208.Span a (k+1) p:ℤ)≤(N:ℤ)-1 then 1 else 0)) := by
  classical
  let gates : ℕ := (if d*(a:ℤ)≤(N:ℤ)-1 then 1 else 0)+
    (if d*(ResidualSpan208.Span a (k+1) p:ℤ)≤(N:ℤ)-1 then 1 else 0)
  change ∑ S∈F,(S\P S).card ≤ N*gates
  have fibre (x : ℤ) : F.filter (fun S => x∈S\P S) =
      F.filter (fun S => x∈S\P S ∧ (S\P S).card<k+1) := by
    ext S
    simp only [Finset.mem_filter]
    exact ⟨fun ⟨h,m⟩ => ⟨h,m,by have := few S h; omega⟩,fun ⟨h,m,_⟩ => ⟨h,m⟩⟩
  have cap (x : ℤ) (_ : x∈Ground N) : (F.filter (fun S => x∈S\P S)).card≤gates := by
    rw [fibre x]
    exact ResidualOccupancy208.actual_cumulative_occupancy (b:=k+1)
      legal two P core stride pivot large longest proper x
  simpa only [ground_card,Nat.mul_comm gates] using
    ResidualPool208.incidence_capacity F (Ground N) (fun S => S\P S) gates
      (fun S hs => Finset.sdiff_subset.trans (legal.1 S hs)) cap

#print axioms marked_overlap
#print axioms marked_weight
end JSP233.MarkedCoreEnds20258
