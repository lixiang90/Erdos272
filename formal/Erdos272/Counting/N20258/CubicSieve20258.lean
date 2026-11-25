module

public import Erdos272.Arithmetic.N20258.PairError20258
public import Erdos272.Counting.N20258.Bonferroni20258
public import Erdos272.Counting.N88404.InclusionExclusion88404

@[expose] public section
namespace JSP233.CubicSieve20258
open InclusionExclusion88404
open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false

def density (p : ℕ) : ℚ := 1 / (p : ℚ)^3

/-- Alternating elementary symmetric sums, through the specified degree. -/
def coefficient : List ℕ → ℕ → ℚ
  | [], _ => 1
  | _::_, 0 => 1
  | p::ps, k+1 => coefficient ps (k+1) - density p * coefficient ps k

def factor (v : ℕ → ℚ) (K : Finset ℕ) : ℚ := ∏ p ∈ K, v p

private def cut (count : Finset ℕ → ℚ) : List ℕ → ℕ → Finset ℕ → ℚ
  | [], _, K => count K
  | _::_, 0, K => count K
  | p::ps, k+1, K => cut count ps (k+1) K - cut count ps k (insert p K)

private theorem cut_zero (count : Finset ℕ → ℚ) (ps : List ℕ) (K : Finset ℕ) :
    cut count ps 0 K = count K := by cases ps <;> rfl

private theorem coefficient_zero (ps : List ℕ) : coefficient ps 0 = 1 := by
  cases ps <;> rfl

private theorem split_insert (p : ℕ) (ps : List ℕ) (K B : Finset ℕ)
    (hL : ∀ j ∈ p::ps, j ∈ B) (nd : (p::ps).Nodup) (hK : K ⊆ B)
    (apart : ∀ j ∈ p::ps, j ∉ K) :
    insert p K ⊆ B ∧ (∀ j ∈ ps, j ∉ insert p K) := by
  refine ⟨Finset.insert_subset (hL p List.mem_cons_self) hK, ?_⟩
  intro j hj h
  rcases Finset.mem_insert.mp h with rfl | h
  · exact (List.nodup_cons.mp nd).1 hj
  · exact apart j (List.mem_cons_of_mem _ hj) h

/-- The only error for the first-order lower bound is the error at its root. -/
private theorem first (B : Finset ℕ) (count : Finset ℕ → ℚ) (S E : ℚ)
    (upper : ∀ K ⊆ B, count K ≤ S * factor density K)
    (lower : ∀ K ⊆ B, S * factor density K - E * factor PairError20258.reciprocal K ≤ count K)
    (ps : List ℕ) (hL : ∀ j ∈ ps, j ∈ B) (K : Finset ℕ) (hK : K ⊆ B)
    (apart : ∀ j ∈ ps, j ∉ K) :
    S * factor density K * coefficient ps 1 - E * factor PairError20258.reciprocal K ≤
      cut count ps 1 K := by
  induction ps with
  | nil => simpa [cut, coefficient] using lower K hK
  | cons p ps ih =>
    have htail := ih (fun j hj => hL j (List.mem_cons_of_mem _ hj))
      (fun j hj => apart j (List.mem_cons_of_mem _ hj))
    have hi := upper (insert p K) (Finset.insert_subset (hL p List.mem_cons_self) hK)
    have hp := apart p List.mem_cons_self
    rw [factor, Finset.prod_insert hp] at hi
    change count (insert p K) ≤ S * (density p * factor density K) at hi
    rw [cut, cut_zero, coefficient, coefficient_zero]
    linarith only [htail, hi]

/-- At second order each later single reciprocal pays one boundary error. -/
private theorem second (B : Finset ℕ) (count : Finset ℕ → ℚ) (S E : ℚ)
    (upper : ∀ K ⊆ B, count K ≤ S * factor density K)
    (lower : ∀ K ⊆ B, S * factor density K - E * factor PairError20258.reciprocal K ≤ count K)
    (ps : List ℕ) (hL : ∀ j ∈ ps, j ∈ B) (nd : ps.Nodup)
    (K : Finset ℕ) (hK : K ⊆ B) (apart : ∀ j ∈ ps, j ∉ K) :
    cut count ps 2 K ≤ S * factor density K * coefficient ps 2 +
      E * factor PairError20258.reciprocal K * (ps.map PairError20258.reciprocal).sum := by
  induction ps with
  | nil => simpa [cut, coefficient] using upper K hK
  | cons p ps ih =>
    have hL' : ∀ j ∈ ps, j ∈ B := fun j hj => hL j (List.mem_cons_of_mem _ hj)
    have htail := ih hL' (List.nodup_cons.mp nd).2
      (fun j hj => apart j (List.mem_cons_of_mem _ hj))
    obtain ⟨hI,hA⟩ := split_insert p ps K B hL nd hK apart
    have hb := first B count S E upper lower ps hL' (insert p K) hI hA
    have hp := apart p List.mem_cons_self
    simp only [factor, Finset.prod_insert hp] at hb
    change S * (density p * factor density K) * coefficient ps 1 -
      E * (PairError20258.reciprocal p * factor PairError20258.reciprocal K) ≤ _ at hb
    rw [cut, coefficient, List.map_cons, List.sum_cons]
    linarith only [htail, hb]

private theorem third (B : Finset ℕ) (count : Finset ℕ → ℚ) (S E : ℚ)
    (empty : count ∅ = S)
    (upper : ∀ K ⊆ B, count K ≤ S * factor density K)
    (lower : ∀ K ⊆ B, S * factor density K - E * factor PairError20258.reciprocal K ≤ count K)
    (ps : List ℕ) (hL : ∀ j ∈ ps, j ∈ B) (nd : ps.Nodup) :
    S * coefficient ps 3 - E * PairError20258.pairs ps ≤ cut count ps 3 ∅ := by
  induction ps with
  | nil => simp [cut, coefficient, PairError20258.pairs, empty]
  | cons p ps ih =>
    have hL' : ∀ j ∈ ps, j ∈ B := fun j hj => hL j (List.mem_cons_of_mem _ hj)
    obtain ⟨hp,hnd⟩ := List.nodup_cons.mp nd
    have htail := ih hL' hnd
    have hb := second B count S E upper lower ps hL' hnd {p}
      (Finset.singleton_subset_iff.mpr (hL p List.mem_cons_self))
      (by intro j hj; simpa only [Finset.mem_singleton] using (fun e => hp (e ▸ hj) : j ≠ p))
    simp only [factor, Finset.prod_singleton] at hb
    rw [cut, Finset.insert_empty, coefficient, PairError20258.pairs]
    linarith only [htail, hb]

private theorem cut_intersections {α : Type*} [DecidableEq α]
    (R : Finset α) (P : ℕ → α → Prop) (ps : List ℕ) (k : ℕ) (K : Finset ℕ) :
    cut (fun J => ((Intersect R P J).card : ℚ)) ps k K =
      (Bonferroni20258.truncated (ps.map (fun p => R.filter (P p))) k (Intersect R P K) : ℚ) := by
  induction ps generalizing k K with
  | nil => simp [cut, Bonferroni20258.truncated]
  | cons p ps ih =>
    cases k with
    | zero => simp [cut, Bonferroni20258.truncated]
    | succ k =>
      have he : Intersect R P (insert p K) = Intersect R P K ∩ R.filter (P p) := by
        ext x
        simp [Intersect]
        tauto
      simp only [cut, List.map_cons, Bonferroni20258.truncated, Int.cast_sub, ih, he]

private theorem remaining_avoid {α : Type*} [DecidableEq α]
    (R : Finset α) (P : ℕ → α → Prop) (ps : List ℕ) :
    Bonferroni20258.remaining (ps.map (fun p => R.filter (P p))) R = Avoid R P ps.toFinset := by
  induction ps with
  | nil => simp [Bonferroni20258.remaining, Avoid]
  | cons p ps ih =>
    simp only [List.map_cons, Bonferroni20258.remaining, ih, List.toFinset_cons]
    ext x
    simp [Avoid]
    tauto

/-- Only pair intersections pay a boundary error. The size of the complement
is computed on the original set with its actual phase predicates. -/
theorem priced {α : Type*} [DecidableEq α] (R : Finset α) (P : ℕ → α → Prop)
    (ps : List ℕ) (nd : ps.Nodup) (E : ℚ)
    (upper : ∀ K ⊆ ps.toFinset, ((Intersect R P K).card : ℚ) ≤ R.card * factor density K)
    (lower : ∀ K ⊆ ps.toFinset, R.card * factor density K -
      E * factor PairError20258.reciprocal K ≤ (Intersect R P K).card) :
    R.card * coefficient ps 3 - E * PairError20258.pairs ps ≤ (Avoid R P ps.toFinset).card := by
  have h := third ps.toFinset (fun J => ((Intersect R P J).card : ℚ)) R.card E
    (by simp [intersect_empty]) upper lower ps (by simp) nd
  rw [cut_intersections, intersect_empty] at h
  have hb := Bonferroni20258.third_lower (ps.map (fun p => R.filter (P p))) R
  rw [remaining_avoid] at hb
  exact h.trans (by exact_mod_cast hb)

#print axioms priced
end
end JSP233.CubicSieve20258
