module

public import Erdos272.Counting.N20258.ShortTransversal20258

@[expose] public section

namespace JSP233.MixedOmitter20258
open StarCompletion SparseSmall39 AnchorCompletion38 PrivatePairExistence
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false

/-- The test member can itself be an AP. Only members being counted in
the first-hit classes need to be crooked. -/
theorem actual_degree {N : ℕ} {F : Finset (Finset ℤ)} {c : ℤ} {T : Finset ℤ}
    (hF : Legal (Ground N) F) (hT : T ∈ F) (miss : c ∉ T) :
    (RootPart (CrookedMembers F) c).card ≤ DegreeBudget N T.card := by
  let H := RootPart (CrookedMembers F) c
  have rooted {S : Finset ℤ} (hS : S ∈ H) : S ∈ RootPart F c := by
    obtain ⟨hSC,hc⟩ := Finset.mem_filter.mp hS
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hSC).1,hc⟩
  have maps (S : Finset ℤ) (hS : S ∈ H) : Hit T S ∈ T :=
    (Finset.mem_inter.mp (hit_spec (rooted_member_hits_omitter hF hT miss (rooted hS))).1).2
  have bound (x : ℤ) (hx : x ∈ T) :
      (H.filter (fun S => Hit T S = x)).card ≤ N-(Earlier T x).card-2 := by
    let C := H.filter (fun S => Hit T S = x)
    change C.card ≤ _
    by_cases ne : C.Nonempty
    · have hits {S : Finset ℤ} (hS : S ∈ C) : S ∈ HitClass F c T x := by
        obtain ⟨hSH,hh⟩ := Finset.mem_filter.mp hS
        exact Finset.mem_filter.mpr ⟨rooted hSH,hh⟩
      have sub : C ⊆ F := fun _ hS =>
        (Finset.mem_filter.mp (rooted (Finset.mem_filter.mp hS).1)).1
      have legal : Legal (Ground N\Earlier T x) C := by
        refine ⟨?_, fun S hS U hU => hF.2 S (sub hS) U (sub hU)⟩
        intro S hS y hy
        exact Finset.mem_sdiff.mpr ⟨hF.1 S (sub hS) hy, fun he =>
          Finset.disjoint_left.mp (hitClass_avoids_earlier hF hT miss (hits hS)) hy he⟩
      have hxS (S : Finset ℤ) (hS : S ∈ C) : x ∈ S := by
        obtain ⟨hSH,he⟩ := Finset.mem_filter.mp hS
        have hh := (Finset.mem_inter.mp
          (hit_spec (rooted_member_hits_omitter hF hT miss (rooted hSH))).1).1
        rwa [he] at hh
      have cap := actual_two_point_crooked_ground_capacity (Ground N\Earlier T x) C c x
        (by rintro rfl; exact miss hx) ne legal
        (fun _ hS => (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).1).2)
        (fun _ hS => (Finset.mem_filter.mp (rooted (Finset.mem_filter.mp hS).1)).2) hxS
      have subT : Earlier T x ⊆ Ground N := (Finset.filter_subset _ _).trans (hF.1 T hT)
      have card := Finset.card_sdiff_add_card_eq_card subT
      rw [ground_card] at card
      omega
    · simp [Finset.not_nonempty_iff_eq_empty.mp ne]
  change H.card ≤ _
  calc
    H.card = ∑ x ∈ T, (H.filter (fun S => Hit T S = x)).card :=
      Finset.card_eq_sum_card_fiberwise maps
    _ ≤ ∑ x ∈ T, (N-(Earlier T x).card-2) := Finset.sum_le_sum bound
    _ = _ := sum_earlier_function T (fun i => N-i-2)

theorem actual_quadratic {N : ℕ} {F : Finset (Finset ℤ)} {c : ℤ} {T : Finset ℤ}
    (hN : 2 ≤ N) (hF : Legal (Ground N) F) (hT : T ∈ F) (miss : c ∉ T)
    (hs : T.card+1 ≤ N) :
    ((RootPart (CrookedMembers F) c).card : ℝ) ≤ ShortTransversal20258.rootPrice N T.card := by
  have h : ((RootPart (CrookedMembers F) c).card : ℝ) ≤ DegreeBudget N T.card := by
    exact_mod_cast actual_degree hF hT miss
  have he := congrArg (fun k : ℕ => (k : ℝ)) (degreeBudget_closed N T.card hN hs)
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hN, Nat.cast_ofNat, Nat.cast_choose_two] at he
  unfold ShortTransversal20258.rootPrice
  nlinarith only [h,he]

#print axioms actual_quadratic
end
end JSP233.MixedOmitter20258
