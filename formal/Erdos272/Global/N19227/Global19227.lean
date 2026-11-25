module

public import Erdos272.Global.N19227.Unrooted19227
public import Erdos272.Global.N20258.Global20258
public import Erdos272.Global.N20258.RootedFamily20258

@[expose] public section
namespace JSP233.Global19227
open StarCompletion DenseDeletion40
set_option autoImplicit false

/-- The upper bound on the original legal family. In the first window,
the retained crooked members either have a common root or admit a first
sparse cutoff. -/
theorem actual_original_upper_bound {N : ℕ} {F : Finset (Finset ℤ)}
    (lo : 19227 ≤ N) (legal : Legal (Ground N) F) : F.card ≤ B N := by
  by_cases later : 20258 ≤ N
  · exact Global20258.actual_original_upper_bound later legal
  by_cases common : ∃ c ∈ Ground N, ∀ S ∈ Retained N 12 F, ¬IsAP S → c ∈ S
  · exact RootedFamily20258.actual_upper_from_19227 lo (by omega) legal common
  · exact Credit19227.unrooted_upper lo (by omega) legal common

theorem actual_value_eq_B (N : ℕ) (lo : 19227 ≤ N) : ExtremalValue45.Value N = B N := by
  apply (ExtremalValue45.exact_value_iff_actual_upper N (by omega)).mpr
  exact fun _ legal => actual_original_upper_bound lo legal

theorem actual_optimal_family (N : ℕ) (lo : 19227 ≤ N) :
    ∃ F : Finset (Finset ℤ), Legal (Ground N) F ∧ F.card = B N ∧
      ∀ G : Finset (Finset ℤ), Legal (Ground N) G → G.card ≤ F.card := by
  obtain ⟨F, legal, card⟩ := Construction45.szabo_lower_construction N (by omega)
  exact ⟨F, legal, card, fun G hG => by simpa only [card] using actual_original_upper_bound lo hG⟩

end JSP233.Global19227
