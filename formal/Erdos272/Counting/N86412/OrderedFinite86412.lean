module

public import Erdos272.Core.FarShort112

@[expose] public section

namespace JSP233.OrderedFinite86412
open StarCompletion APGeometry
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def Grid (a d : ℤ) (m : ℕ) : Finset ℤ :=
  (Finset.range m).image (fun i : ℕ => a + (i : ℤ) * d)

theorem mem_grid {a d x : ℤ} {m : ℕ} :
    x ∈ Grid a d m ↔ ∃ i < m, x = a + (i : ℤ) * d := by
  constructor
  · intro hx
    obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hx
    exact ⟨i, Finset.mem_range.mp hi, he.symm⟩
  · rintro ⟨i, hi, he⟩
    exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, he.symm⟩

theorem grid_card {a d : ℤ} (hd : 0 < d) (m : ℕ) :
    (Grid a d m).card = m := by
  unfold Grid
  rw [Finset.card_image_of_injOn, Finset.card_range]
  intro i hi j hj he
  have hij : (i : ℤ) = (j : ℤ) := by nlinarith
  exact_mod_cast hij

theorem grid_apAt {a d : ℤ} (hd : 0 < d) (m : ℕ) :
    APAt d a (Grid a d m) := by
  refine ⟨hd, a, a + ((m : ℤ) - 1) * d, ?_⟩
  intro x
  constructor
  · intro hx
    obtain ⟨i, hi, rfl⟩ := mem_grid.mp hx
    have him : (i : ℤ) < (m : ℤ) := by exact_mod_cast hi
    refine ⟨?_, ?_, ?_⟩
    · nlinarith [Int.natCast_nonneg i]
    · nlinarith
    · exact ⟨(i : ℤ), by ring⟩
  · rintro ⟨hlo, hhi, k, hk⟩
    have hk0 : 0 ≤ k := by nlinarith
    have hkm : k < (m : ℤ) := by nlinarith
    have he : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hk0
    apply mem_grid.mpr
    refine ⟨k.toNat, ?_, ?_⟩
    · omega
    · rw [he]
      nlinarith only [hk]

theorem grid_isAP {a d : ℤ} (hd : 0 < d) {m : ℕ} (hm : 0 < m) :
    IsAP (Grid a d m) := by
  apply (isAP_iff_exists_APAt _).mpr
  refine ⟨d, a, grid_apAt hd m, ?_⟩
  exact mem_grid.mpr ⟨0, hm, by simp⟩

abbrev point (S : Finset ℤ) (i : ℕ) : ℤ := FarShort112.point S i

theorem point_surjective {S : Finset ℤ} {x : ℤ} (hx : x ∈ S) :
    ∃ i < S.card, point S i = x := by
  let i : Fin S.card := (S.orderIsoOfFin rfl).symm ⟨x, hx⟩
  refine ⟨i.val, i.isLt, ?_⟩
  simp only [point, FarShort112.point, dif_pos i.isLt]
  exact congrArg Subtype.val ((S.orderIsoOfFin rfl).apply_symm_apply ⟨x, hx⟩)

theorem consecutive_no_between {S : Finset ℤ} {i : ℕ} (hi : i + 1 < S.card) :
    ∀ t ∈ S, point S i < t → t < point S (i + 1) → False := by
  intro t ht hlo hhi
  exact (FarShort112.actual_adjacent_gap (by omega : i < S.card - 1)).2.2.2
    t ht ⟨hlo, hhi⟩

theorem equal_consecutive_gaps {S : Finset ℤ} (hS : 2 ≤ S.card)
    (H : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x < y → y < z →
      (∀ t ∈ S, x < t → t < y → False) →
      (∀ t ∈ S, y < t → t < z → False) → y - x = z - y) :
    ∃ a d : ℤ, 0 < d ∧ S = Grid a d S.card := by
  let a := point S 0
  let d := point S 1 - point S 0
  have hd : 0 < d := by
    have hh := FarShort112.point_strict (S := S) (by decide : 0 < 1)
      (by omega : 1 < S.card)
    change 0 < FarShort112.point S 1 - FarShort112.point S 0
    exact sub_pos.mpr hh
  have hgap : ∀ i : ℕ, i + 2 < S.card →
      point S (i + 1) - point S i = point S (i + 2) - point S (i + 1) := by
    intro i hi
    apply H (point S i) (FarShort112.point_mem (by omega))
      (point S (i + 1)) (FarShort112.point_mem (by omega))
      (point S (i + 2)) (FarShort112.point_mem hi)
    · exact FarShort112.point_strict (by omega) (by omega)
    · exact FarShort112.point_strict (by omega) hi
    · exact consecutive_no_between (by omega)
    · simpa only [Nat.add_assoc] using
        consecutive_no_between (S := S) (i := i + 1) (by omega)
  have hfixed : ∀ i : ℕ, i + 1 < S.card → point S (i + 1) - point S i = d := by
    intro i
    induction i with
    | zero => intro hi; rfl
    | succ i ih =>
      intro hi
      have hp := ih (by omega)
      have hn := hgap i (by omega)
      simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using hn.symm.trans hp
  have hvalue : ∀ i : ℕ, i < S.card → point S i = a + (i : ℤ) * d := by
    intro i
    induction i with
    | zero => intro hi; simp [a]
    | succ i ih =>
      intro hi
      have hp := ih (by omega)
      have hg := hfixed i (by omega)
      norm_num only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one]
      nlinarith only [hp, hg]
  refine ⟨a, d, hd, ?_⟩
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi, rfl⟩ := point_surjective hx
    exact mem_grid.mpr ⟨i, hi, hvalue i hi⟩
  · intro hx
    obtain ⟨i, hi, rfl⟩ := mem_grid.mp hx
    rw [← hvalue i hi]
    exact FarShort112.point_mem hi

theorem apAt_of_equal_consecutive_gaps {S : Finset ℤ} (hS : 2 ≤ S.card)
    (H : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x < y → y < z →
      (∀ t ∈ S, x < t → t < y → False) →
      (∀ t ∈ S, y < t → t < z → False) → y - x = z - y) :
    ∃ a d : ℤ, 0 < d ∧ APAt d a S ∧ S = Grid a d S.card := by
  obtain ⟨a, d, hd, he⟩ := equal_consecutive_gaps hS H
  refine ⟨a, d, hd, ?_, he⟩
  rw [he]
  exact grid_apAt hd _

theorem isAP_of_equal_consecutive_gaps {S : Finset ℤ} (hS : 2 ≤ S.card)
    (H : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x < y → y < z →
      (∀ t ∈ S, x < t → t < y → False) →
      (∀ t ∈ S, y < t → t < z → False) → y - x = z - y) :
    IsAP S := by
  obtain ⟨a, d, hd, he⟩ := equal_consecutive_gaps hS H
  rw [he]
  exact grid_isAP hd (by omega)

#print axioms mem_grid
#print axioms grid_card
#print axioms grid_apAt
#print axioms grid_isAP
#print axioms point_surjective
#print axioms consecutive_no_between
#print axioms equal_consecutive_gaps
#print axioms apAt_of_equal_consecutive_gaps
#print axioms isAP_of_equal_consecutive_gaps
end
end JSP233.OrderedFinite86412
