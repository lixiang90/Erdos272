module

public import Erdos272.Global.RootQuadratic208
public import Erdos272.Foundation.PrivatePairExistence
public import Erdos272.Counting.Density41

@[expose] public section

/-! A progression in the original family meets every crooked member. This
allows the size of the shortest progression to bound the entire crooked
family, before taking its sparse part or padding the ground set. -/
namespace JSP233.ShortTransversal20258

open StarCompletion PrivatePairExistence Density41
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false

/-- The omitter bound, in the original ground set. -/
def rootPrice (N m : ℕ) : ℝ := m * (N : ℝ) - ((m : ℝ)^2 + 3*m)/2

theorem rootPrice_mono {N t m : ℕ} (ht : t ≤ m) (hm : m+2 ≤ N) :
    rootPrice N t ≤ rootPrice N m := by
  have ht' : (t : ℝ) ≤ m := by exact_mod_cast ht
  have hm' : (m : ℝ)+2 ≤ N := by exact_mod_cast hm
  have h := mul_nonneg (sub_nonneg.mpr ht')
    (show 0 ≤ (N : ℝ)-((m : ℝ)+t+3)/2 by linarith)
  unfold rootPrice
  nlinarith only [h]

/-- Each member counted here is represented by at least one incidence with
the transversal. No assumption about overlaps among incidences is needed. -/
theorem card_le_sum_degrees {H : Finset (Finset ℤ)} {P : Finset ℤ}
    (h : ∀ S ∈ H, (P ∩ S).Nonempty) :
    H.card ≤ ∑ x ∈ P, (RootPart H x).card := by
  have cover : H ⊆ P.biUnion (RootPart H) := by
    intro S hS
    obtain ⟨x,hx⟩ := h S hS
    obtain ⟨hxP,hxS⟩ := Finset.mem_inter.mp hx
    exact Finset.mem_biUnion.mpr ⟨x,hxP,Finset.mem_filter.mpr ⟨hS,hxS⟩⟩
  exact (Finset.card_le_card cover).trans Finset.card_biUnion_le

/-- An actual progression of length `P.card` in a legal family bounds
*all* crooked members when each of its points has a small crooked omitter. -/
theorem actual_short_transversal {N m : ℕ} {F : Finset (Finset ℤ)} {P : Finset ℤ}
    (hN : 2 ≤ N) (hm : m+2 ≤ N) (hF : Legal (Ground N) F)
    (hP : P ∈ F) (hAP : IsAP P)
    (homit : ∀ x ∈ P, ∃ T ∈ CrookedMembers F, x ∉ T ∧ T.card ≤ m) :
    ((CrookedMembers F).card : ℝ) ≤ P.card * rootPrice N m := by
  have hsub : CrookedMembers F ⊆ F := Finset.filter_subset _ _
  have hbad : ∀ S ∈ CrookedMembers F, ¬IsAP S := fun _ hS => (Finset.mem_filter.mp hS).2
  have hlegal : Legal (Ground N) (CrookedMembers F) :=
    ⟨fun S hS => hF.1 S (hsub hS), fun S hS T hT => hF.2 S (hsub hS) T (hsub hT)⟩
  have hhit (S : Finset ℤ) (hS : S ∈ CrookedMembers F) : (P ∩ S).Nonempty :=
    isAP_nonempty (hF.2 P hP S (hsub hS) (fun he => hbad S hS (he ▸ hAP)))
  have hdeg (x : ℤ) (hx : x ∈ P) :
      ((RootPart (CrookedMembers F) x).card : ℝ) ≤ rootPrice N m := by
    obtain ⟨T,hT,hxT,ht⟩ := homit x hx
    exact (RootQuadratic208.actual_omitter_quadratic hN hlegal hbad hT hxT (by omega)).trans
      (rootPrice_mono ht hm)
  have hc := card_le_sum_degrees hhit
  calc
    ((CrookedMembers F).card : ℝ) ≤ ∑ x ∈ P, ((RootPart (CrookedMembers F) x).card : ℝ) := by
      exact_mod_cast hc
    _ ≤ ∑ _x ∈ P, rootPrice N m := Finset.sum_le_sum hdeg
    _ = P.card * rootPrice N m := by simp

/-- The small crooked sets used to choose the empty kernel are the same
on every larger padded ground as soon as the cutoff is sparse on the
original ground. -/
theorem small_sparse_eq {N U r m : ℕ} (hs : r*m ≤ N) (hNU : N ≤ U)
    (F : Finset (Finset ℤ)) :
    (SparseCrooked U r F).filter (fun S => S.card ≤ m) =
      (CrookedMembers F).filter (fun S => S.card ≤ m) := by
  ext S
  simp only [Finset.mem_filter, actual_sparse_membership, CrookedMembers]
  constructor
  · rintro ⟨⟨hF,hbad,_⟩,hcard⟩
    exact ⟨⟨hF,hbad⟩,hcard⟩
  · rintro ⟨⟨hF,hbad⟩,hcard⟩
    exact ⟨⟨hF,hbad,(Nat.mul_le_mul_left r hcard).trans (hs.trans hNU)⟩,hcard⟩

end
end JSP233.ShortTransversal20258
