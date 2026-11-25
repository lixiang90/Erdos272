module

public import Erdos272.Resources.ActualExterior208

@[expose] public section
namespace JSP233.RootedExterior20258
open StarCompletion APGeometry APCount41 APPrepare49 PreparedClasses50 HarmonicAbel29
open scoped Classical
noncomputable section
set_option autoImplicit false

/-- A nonunit exterior progression now contains the root, so its left
endpoint lies in the first c sites of the ground set. -/
theorem actual {N c L R : ℕ} {G : Finset (Finset ℤ)} (rn : R ≤ N) (legal : Legal (Ground N) G)
    (unit : ∀ S ∈ G, IsAP S → (c : ℤ) ∉ S → Step S=1) :
    ((EX (PreparedAP G c L) R).card : ℝ) ≤
      (129/200 : ℝ)*c*((N : ℝ)-R)+((c : ℝ)+(N-R))*Harmonic N+N := by
  let U := EX (PreparedAP G c L) R
  have data (S : Finset ℤ) (hs : S ∈ U) :
      S ∈ G ∧ IsAP S ∧ 4 ≤ S.card ∧ 2 ≤ Step S ∧ (R : ℤ) ≤ High S := by
    obtain ⟨h,step,high⟩ := Finset.mem_filter.mp hs
    obtain ⟨hG,ap,large,_⟩ := actual_prepared_AP_member h
    exact ⟨hG,ap,large,step,high⟩
  have sub : U ⊆ G := fun S hs => (data S hs).1
  have legalU : Legal (Ground N) U :=
    ⟨fun S hs => legal.1 S (sub hs),fun S hs T ht => legal.2 S (sub hs) T (sub ht)⟩
  apply ActualExterior208.actual_large_step_endpoint_width rn legalU
    (fun S hs => (data S hs).2.1) (fun S hs => by have := (data S hs).2.2.1; omega)
    (fun S hs => (data S hs).2.2.2.1)
  intro S hs
  obtain ⟨h,ap,_,step,high⟩ := data S hs
  have hit : (c : ℤ) ∈ S := by
    by_contra miss
    have one := unit S h ap miss
    omega
  exact ⟨(low_spec (isAP_nonempty ap)).2 _ hit,high⟩

#print axioms actual
end
end JSP233.RootedExterior20258
