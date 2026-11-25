module

public import Erdos272.Resources.SourceBridge208
public import Erdos272.Geometry.AffineLine30
public import Mathlib.Algebra.BigOperators.Intervals

@[expose] public section

namespace JSP233.APCodeContraction118533
open StarCompletion SourceBridge208 ActualAPCount208 AffineLine30 StaircaseGeometry
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

def Ends (S : Finset ℤ) (q : ℕ) : Finset (ℤ × ℤ) := Codes S q \ Codes S (q+1)

theorem codes_succ_subset (S : Finset ℤ) (q : ℕ) : Codes S (q+1) ⊆ Codes S q := by
  intro p hp
  obtain ⟨hx, hy, hxy, hall⟩ := mem_codes.mp hp
  exact mem_codes.mpr ⟨hx, hy, hxy, fun j hj => hall j (by omega)⟩

theorem mem_ends {S : Finset ℤ} {q : ℕ} {p : ℤ × ℤ} :
    p ∈ Ends S q ↔ p ∈ Codes S q ∧ Point p (q+1) ∉ S := by
  constructor
  · intro hp
    obtain ⟨hp, hn⟩ := Finset.mem_sdiff.mp hp
    refine ⟨hp, ?_⟩
    intro hx
    apply hn
    obtain ⟨hu, hv, huv, hall⟩ := mem_codes.mp hp
    refine mem_codes.mpr ⟨hu, hv, huv, ?_⟩
    intro j hj
    by_cases h : j ≤ q
    · exact hall j h
    · have he : j = q+1 := by omega
      simpa only [he] using hx
  · rintro ⟨hp, hn⟩
    exact Finset.mem_sdiff.mpr ⟨hp, fun hh => hn ((mem_codes.mp hh).2.2.2 (q+1) le_rfl)⟩

theorem prefix_mem_ends {S : Finset ℤ} {q : ℕ} (hq : 1 ≤ q)
    {p : ℤ × ℤ} (hp : p ∈ Ends S (q+1)) : Prefix p ∈ Ends S q := by
  obtain ⟨hp, hn⟩ := mem_ends.mp hp
  obtain ⟨hx, hy, hxy, hall⟩ := mem_codes.mp hp
  apply mem_ends.mpr
  constructor
  · apply mem_codes.mpr
    refine ⟨?_, hx, ?_, ?_⟩
    · have hh := hall 2 (by omega)
      have he : Point p 2 = (Prefix p).1 := by simp only [Point, Prefix]; ring
      rwa [he] at hh
    · dsimp only [Prefix]
      omega
    · intro j hj
      rw [point_prefix]
      exact hall (j+1) (by omega)
  · simpa only [point_prefix] using hn

theorem ends_succ_card_le {S : Finset ℤ} {q : ℕ} (hq : 1 ≤ q) :
    (Ends S (q+1)).card ≤ (Ends S q).card := by
  apply Finset.card_le_card_of_injOn Prefix
  · intro p hp
    exact prefix_mem_ends hq hp
  · exact prefix_injective.injOn

theorem ends_card_antitone {S : Finset ℤ} {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) :
    (Ends S j).card ≤ (Ends S i).card := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih => exact (ends_succ_card_le (by omega : 1 ≤ j)).trans ih

theorem count_split (S : Finset ℤ) (q : ℕ) :
    (Ends S q).card+(Codes S (q+1)).card = (Codes S q).card := by
  rw [Ends, Finset.card_sdiff_of_subset (codes_succ_subset S q)]
  exact Nat.sub_add_cancel (Finset.card_le_card (codes_succ_subset S q))

theorem codes_empty_of_max {S : Finset ℤ} {a : ℕ} (hmax : MaxAPSize S ≤ a) :
    Codes S a = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  obtain ⟨hx, hy, hxy, hall⟩ := mem_codes.mp hp
  let d := p.2-p.1
  have hd : 0 < d := by dsimp only [d]; omega
  have hsub : mapSet p.2 d (Window a 0) ⊆ S := by
    intro x hx
    obtain ⟨z, hz, he⟩ := Finset.mem_image.mp hx
    have hz' : -(a : ℤ) ≤ z ∧ z ≤ 0 := by simpa only [Window, Finset.mem_Icc, Nat.cast_zero] using hz
    let j := (-z).toNat
    have hj : (j : ℤ) = -z := Int.toNat_of_nonneg (by omega)
    have hja : j ≤ a := by omega
    have hPoint : Point p j = x := by
      dsimp only [Point]
      rw [hj]
      dsimp only [affine, d] at he
      nlinarith only [he]
    rw [← hPoint]
    exact hall j hja
  have hAP := affine_isAP p.2 d hd (window_isAP a 0)
  have hc := (AP_card_le_max hAP hsub).trans hmax
  rw [mapSet_card _ _ hd, window_card] at hc
  omega

theorem count_eq_sum_ends {S : Finset ℤ} {a q : ℕ} (hqa : q ≤ a)
    (ha : Codes S a = ∅) : (Codes S q).card = ∑ j ∈ Finset.Ico q a, (Ends S j).card := by
  have aux : ∀ k q, a = q+k →
      (Codes S q).card = ∑ j ∈ Finset.Ico q a, (Ends S j).card := by
    intro k
    induction k with
    | zero =>
        intro q he
        have hq : q = a := by omega
        simp only [hq, ha, Finset.card_empty, Finset.Ico_self, Finset.sum_empty]
    | succ k ih =>
        intro q he
        have hq : q < a := by omega
        have hs := ih (q+1) (by omega)
        have hc := count_split S q
        rw [Finset.sum_eq_sum_Ico_succ_bot hq]
        omega
  exact aux (a-q) q (by omega)

theorem count_contraction {S : Finset ℤ} {a h q : ℕ}
    (hh : 1 ≤ h) (hhq : h ≤ q) (hqa : q < a) (hmax : MaxAPSize S ≤ a) :
    (a-h)*(Codes S q).card ≤ (a-q)*(Codes S h).card := by
  have hz := codes_empty_of_max hmax
  have ht := count_eq_sum_ends hqa.le hz
  have hh' := count_eq_sum_ends (hhq.trans hqa.le) hz
  have htail : (∑ j ∈ Finset.Ico q a, (Ends S j).card) ≤
      (a-q)*(Ends S q).card := by
    calc
      _ ≤ ∑ _j ∈ Finset.Ico q a, (Ends S q).card := by
        apply Finset.sum_le_sum
        intro j hj
        exact ends_card_antitone (hh.trans hhq) (Finset.mem_Ico.mp hj).1
      _ = _ := by simp
  have hhead : (q-h)*(Ends S q).card ≤ ∑ j ∈ Finset.Ico h q, (Ends S j).card := by
    calc
      _ = ∑ _j ∈ Finset.Ico h q, (Ends S q).card := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro j hj
        exact ends_card_antitone (hh.trans (Finset.mem_Ico.mp hj).1)
          (Finset.mem_Ico.mp hj).2.le
  have hsplit := Finset.sum_Ico_consecutive (fun j => (Ends S j).card) hhq hqa.le
  have hleft := Nat.mul_le_mul_left (q-h) htail
  have hright := Nat.mul_le_mul_left (a-q) hhead
  have hcoef : a-h = (a-q)+(q-h) := by omega
  rw [← ht] at hleft
  rw [← hh', ← ht] at hsplit
  have hm : (q-h)*(Codes S q).card ≤
      (a-q)*(∑ j ∈ Finset.Ico h q, (Ends S j).card) :=
    hleft.trans (by simpa only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hright)
  rw [hcoef, Nat.add_mul, ← hsplit, Nat.mul_add]
  omega

#print axioms codes_succ_subset
#print axioms mem_ends
#print axioms prefix_mem_ends
#print axioms ends_succ_card_le
#print axioms ends_card_antitone
#print axioms count_split
#print axioms codes_empty_of_max
#print axioms count_eq_sum_ends
#print axioms count_contraction
end
end JSP233.APCodeContraction118533
