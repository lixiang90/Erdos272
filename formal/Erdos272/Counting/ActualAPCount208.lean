module

public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Fintype.Fin
public import Erdos272.Foundation.ProofTactics

@[expose] public section

/-! # Actual finite AP codes

The integer AP extremal argument needed by the intrinsic source bound starts
by splitting at the penultimate point. This file gives that split for actual
integer sets. Codes are the last two points, so their interpretation and both
injections below are exact; there is no cardinality oracle.
-/
namespace JSP233.ActualAPCount208
open scoped Classical BigOperators
noncomputable section

def Point (p : ℤ × ℤ) (j : ℕ) : ℤ :=
  p.2 - (j : ℤ) * (p.2 - p.1)

/-- A code in `Codes S q` describes one increasing AP of `q + 1` points.
Only positive values of `q` are used in the counting theorems. -/
def Codes (S : Finset ℤ) (q : ℕ) : Finset (ℤ × ℤ) :=
  (S.product S).filter fun p => p.1 < p.2 ∧ ∀ j ≤ q, Point p j ∈ S

def OrderedPairs (S : Finset ℤ) : Finset (ℤ × ℤ) :=
  (S.product S).filter fun p => p.1 < p.2

theorem mem_codes {S : Finset ℤ} {q : ℕ} {p : ℤ × ℤ} :
    p ∈ Codes S q ↔ p.1 ∈ S ∧ p.2 ∈ S ∧ p.1 < p.2 ∧
      ∀ j ≤ q, Point p j ∈ S := by
  rcases p with ⟨x, y⟩
  simp only [Codes, Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product, and_assoc]

theorem mem_orderedPairs {S : Finset ℤ} {p : ℤ × ℤ} :
    p ∈ OrderedPairs S ↔ p.1 ∈ S ∧ p.2 ∈ S ∧ p.1 < p.2 := by
  rcases p with ⟨x, y⟩
  simp only [OrderedPairs, Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product, and_assoc]

@[simp] theorem point_zero (p : ℤ × ℤ) : Point p 0 = p.2 := by simp [Point]
@[simp] theorem point_one (p : ℤ × ℤ) : Point p 1 = p.1 := by simp [Point]

theorem codes_one (S : Finset ℤ) : Codes S 1 = OrderedPairs S := by
  ext p
  rw [mem_codes, mem_orderedPairs]
  constructor
  · exact fun h => ⟨h.1, h.2.1, h.2.2.1⟩
  · intro h
    refine ⟨h.1, h.2.1, h.2.2, ?_⟩
    intro j hj
    interval_cases j <;> simpa using (by first | exact h.1 | exact h.2.1)

def Prefix (p : ℤ × ℤ) : ℤ × ℤ := (2 * p.1 - p.2, p.1)

theorem point_prefix (p : ℤ × ℤ) (j : ℕ) :
    Point (Prefix p) j = Point p (j + 1) := by
  simp only [Point, Prefix, Nat.cast_add, Nat.cast_one]
  ring

theorem prefix_injective : Function.Injective Prefix := by
  intro p r h
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  dsimp only [Prefix] at h₁ h₂
  apply Prod.ext <;> omega

/-- Initial segments are specified in the actual integer order. -/
def IsInitial (S T : Finset ℤ) : Prop :=
  T ⊆ S ∧ ∀ x ∈ S, ∀ y ∈ T, x ≤ y → x ∈ T

theorem prefix_mem_of_penultimate {S T : Finset ℤ} {q : ℕ} {p : ℤ × ℤ}
    (hq : 1 ≤ q) (hT : IsInitial S T) (hp : p ∈ Codes S (q + 1))
    (hpT : p.1 ∈ T) : Prefix p ∈ Codes T q := by
  obtain ⟨hx, hy, hxy, hall⟩ := mem_codes.mp hp
  have hpoint : ∀ j ≤ q, Point (Prefix p) j ∈ T := by
    intro j hj
    rw [point_prefix]
    apply hT.2 _ (hall (j + 1) (by omega)) _ hpT
    simp only [Point, Nat.cast_add, Nat.cast_one]
    have hj0 : (0 : ℤ) ≤ j := by positivity
    nlinarith
  apply mem_codes.mpr
  refine ⟨?_, hpT, ?_, hpoint⟩
  · have hh := hpoint 1 hq
    simpa only [point_one] using hh
  · dsimp only [Prefix]
    omega

theorem low_count_le_prefix {S T : Finset ℤ} {q : ℕ}
    (hq : 1 ≤ q) (hT : IsInitial S T) :
    ((Codes S (q + 1)).filter (fun p => p.1 ∈ T)).card ≤ (Codes T q).card := by
  apply Finset.card_le_card_of_injOn Prefix
  · intro p hp
    obtain ⟨hp, hpT⟩ := Finset.mem_filter.mp hp
    exact prefix_mem_of_penultimate hq hT hp hpT
  · exact prefix_injective.injOn

theorem high_subset_pairs {S T : Finset ℤ} {q : ℕ}
    (hT : IsInitial S T) :
    (Codes S q).filter (fun p => p.1 ∉ T) ⊆ OrderedPairs (S \ T) := by
  intro p hp
  obtain ⟨hp, hpT⟩ := Finset.mem_filter.mp hp
  obtain ⟨hx, hy, hxy, _⟩ := mem_codes.mp hp
  apply mem_orderedPairs.mpr
  refine ⟨Finset.mem_sdiff.mpr ⟨hx, hpT⟩, ?_, hxy⟩
  apply Finset.mem_sdiff.mpr
  refine ⟨hy, ?_⟩
  intro hyT
  exact hpT (hT.2 _ hx _ hyT hxy.le)

/-- This is the actual-set recurrence used in the integer AP extremal
argument. The two terms arise from disjoint parts of the same code set. -/
theorem split_count {S T : Finset ℤ} {q : ℕ}
    (hq : 1 ≤ q) (hT : IsInitial S T) :
    (Codes S (q + 1)).card ≤
      (Codes T q).card + (OrderedPairs (S \ T)).card := by
  have hpart := Finset.card_filter_add_card_filter_not
    (s := Codes S (q + 1)) (fun p => p.1 ∈ T)
  have hlo := low_count_le_prefix hq hT
  have hhi := Finset.card_le_card (high_subset_pairs (q := q + 1) hT)
  omega

theorem orderedPairs_card (S : Finset ℤ) :
    (OrderedPairs S).card = S.card.choose 2 := by
  rw [← Finset.card_powersetCard 2 S]
  apply Finset.card_bij (fun p _ => ({p.1, p.2} : Finset ℤ))
  · intro p hp
    obtain ⟨hx, hy, hxy⟩ := mem_orderedPairs.mp hp
    apply Finset.mem_powersetCard.mpr
    constructor
    · exact Finset.insert_subset_iff.mpr ⟨hx, Finset.singleton_subset_iff.mpr hy⟩
    · simp [hxy.ne]
  · intro p hp r hr he
    obtain ⟨_, _, hpord⟩ := mem_orderedPairs.mp hp
    obtain ⟨_, _, hrord⟩ := mem_orderedPairs.mp hr
    have hx : p.1 = r.1 ∨ p.1 = r.2 := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using
        (show p.1 ∈ ({r.1, r.2} : Finset ℤ) by rw [← he]; simp)
    have hy : p.2 = r.1 ∨ p.2 = r.2 := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using
        (show p.2 ∈ ({r.1, r.2} : Finset ℤ) by rw [← he]; simp)
    apply Prod.ext <;> rcases hx with hx | hx <;> rcases hy with hy | hy <;> omega
  · intro Q hQ
    obtain ⟨hQS, hQcard⟩ := Finset.mem_powersetCard.mp hQ
    obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hQcard
    have hx : x ∈ S := hQS (by simp)
    have hy : y ∈ S := hQS (by simp)
    by_cases hlt : x < y
    · exact ⟨(x, y), mem_orderedPairs.mpr ⟨hx, hy, hlt⟩, rfl⟩
    · exact ⟨(y, x), mem_orderedPairs.mpr ⟨hy, hx, by omega⟩, by
        simp only [Finset.pair_comm]⟩

/-- Every finite ordered set has an initial segment of every permitted size. -/
theorem exists_initial_card (S : Finset ℤ) {m : ℕ} (hm : m ≤ S.card) :
    ∃ T : Finset ℤ, IsInitial S T ∧ T.card = m := by
  let f := S.orderEmbOfFin rfl
  let U : Finset (Fin S.card) := Finset.univ.filter fun i => i.val < m
  let T := U.image f
  have hTsub : T ⊆ S := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact S.orderEmbOfFin_mem rfl i
  refine ⟨T, ⟨hTsub, ?_⟩, ?_⟩
  · intro x hx y hy hxy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
    let j : Fin S.card := (S.orderIsoOfFin rfl).symm ⟨x, hx⟩
    have hjx : f j = x := by
      change ((S.orderIsoOfFin rfl) j).val = x
      exact congrArg Subtype.val ((S.orderIsoOfFin rfl).apply_symm_apply ⟨x, hx⟩)
    have hji : j ≤ i := f.le_iff_le.mp (by simpa only [hjx] using hxy)
    apply Finset.mem_image.mpr
    refine ⟨j, ?_, hjx⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ j, lt_of_le_of_lt hji (Finset.mem_filter.mp hi).2⟩
  · rw [Finset.card_image_of_injective U f.injective]
    change (Finset.univ.filter (fun i : Fin S.card => i.val < m)).card = m
    simpa only [Fin.card_filter_val_lt, Nat.min_eq_right hm]

/-- A recursive exact integer-interval bound. Its arithmetic conversion to
the totient source formula is a separate theorem. -/
def Bound (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => n.choose 2
  | q + 2 => Bound (n - n / (q + 2)) (q + 1) + (n / (q + 2)).choose 2

/-- The full geometric induction for arbitrary finite integer sets. -/
theorem count_le_bound (q : ℕ) (hq : 1 ≤ q) (S : Finset ℤ) :
    (Codes S q).card ≤ Bound S.card q := by
  induction q using Nat.strong_induction_on generalizing S with
  | h q ih =>
    match q with
    | 0 => omega
    | 1 => simp only [codes_one, orderedPairs_card, Bound, le_refl]
    | r + 2 =>
      let m := S.card - S.card / (r + 2)
      obtain ⟨T, hT, hcard⟩ := exists_initial_card S
        (show m ≤ S.card from Nat.sub_le _ _)
      have hrec := split_count (q := r + 1) (by omega) hT
      have hprev := ih (r + 1) (by omega) (by omega) T
      have hcomp : (S \ T).card = S.card / (r + 2) := by
        rw [Finset.card_sdiff_of_subset hT.1, hcard]
        have hdiv : S.card / (r + 2) ≤ S.card := Nat.div_le_self _ _
        dsimp only [m]
        exact Nat.sub_sub_self hdiv
      rw [hcard] at hprev
      rw [orderedPairs_card, hcomp] at hrec
      change (Codes S (r + 2)).card ≤
        Bound (S.card - S.card / (r + 2)) (r + 1) + (S.card / (r + 2)).choose 2
      exact hrec.trans (Nat.add_le_add_right hprev _)

#print axioms codes_one
#print axioms prefix_mem_of_penultimate
#print axioms split_count
#print axioms orderedPairs_card
#print axioms exists_initial_card
#print axioms count_le_bound
end
end JSP233.ActualAPCount208
