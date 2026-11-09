module

public import Erdos272.Resources.NeighborSupply208
public import Mathlib.Data.Finset.Sort
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

/-! All three rank classes inject into the same actual physical slot set. -/
namespace JSP233.RankSlots208
open StarCompletion SourceBridge208 PairEnvelope208 PairRanks208 NeighborSupply208
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0

def point (S : Finset ℤ) (i : ℕ) : ℤ :=
  if h : i < S.card then S.orderEmbOfFin rfl ⟨i,h⟩ else 0

theorem point_mem {S : Finset ℤ} {i : ℕ} (hi : i < S.card) : point S i ∈ S := by
  simp only [point, dif_pos hi]
  exact S.orderEmbOfFin_mem rfl ⟨i,hi⟩

theorem point_strict {S : Finset ℤ} {i j : ℕ} (hi : i < j) (hj : j < S.card) :
    point S i < point S j := by
  have his : i < S.card := hi.trans hj
  simp only [point, dif_pos his, dif_pos hj]
  exact (S.orderEmbOfFin rfl).strictMono (show (⟨i,his⟩ : Fin S.card) < ⟨j,hj⟩ from hi)

theorem point_mono {S : Finset ℤ} {i j : ℕ} (hij : i ≤ j) (hj : j < S.card) :
    point S i ≤ point S j := by
  have his : i < S.card := lt_of_le_of_lt hij hj
  simp only [point, dif_pos his, dif_pos hj]
  exact (S.orderEmbOfFin rfl).monotone (show (⟨i,his⟩ : Fin S.card) ≤ ⟨j,hj⟩ from hij)

theorem point_injective {S : Finset ℤ} {i j : ℕ} (hi : i < S.card) (hj : j < S.card)
    (he : point S i = point S j) : i=j := by
  simp only [point, dif_pos hi, dif_pos hj] at he
  exact congrArg Fin.val ((S.orderEmbOfFin rfl).injective he)

theorem point_surjective {S : Finset ℤ} {x : ℤ} (hx : x ∈ S) :
    ∃ j < S.card, point S j = x := by
  let j : Fin S.card := (S.orderIsoOfFin rfl).symm ⟨x,hx⟩
  refine ⟨j.val, j.isLt, ?_⟩
  simp only [point, dif_pos j.isLt]
  exact congrArg Subtype.val ((S.orderIsoOfFin rfl).apply_symm_apply ⟨x,hx⟩)

theorem actual_rank {S : Finset ℤ} {i r : ℕ} (hr : 0 < r) (hi : i+r < S.card) :
    Rank S (point S i) (point S (i+r)) = r := by
  have his : i < S.card := by omega
  have heq : (S.filter fun x => point S i < x ∧ x < point S (i+r)) =
      (Finset.Ioo i (i+r)).image (point S) := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxS, hlo, hhi⟩ := Finset.mem_filter.mp hx
      obtain ⟨j, hjs, rfl⟩ := point_surjective hxS
      have hij : i < j := by
        by_contra hn
        have hh := point_mono (by omega : j ≤ i) his
        omega
      have hjr : j < i+r := by
        by_contra hn
        have hh := point_mono (by omega : i+r ≤ j) hjs
        omega
      exact Finset.mem_image.mpr ⟨j, Finset.mem_Ioo.mpr ⟨hij, hjr⟩, rfl⟩
    · intro hx
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨hij, hjr⟩ := Finset.mem_Ioo.mp hj
      exact Finset.mem_filter.mpr ⟨point_mem (by omega),
        point_strict hij (by omega), point_strict hjr hi⟩
  unfold Rank
  rw [heq, Finset.card_image_of_injOn]
  · rw [Nat.card_Ioo]
    omega
  · intro j hj k hk he
    have hj' := (Finset.mem_Ioo.mp hj).2
    have hk' := (Finset.mem_Ioo.mp hk).2
    exact point_injective (by omega) (by omega) he

def Pairs (S : Finset ℤ) (k : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 k).product (Finset.range S.card)).filter fun p => p.2+p.1 < S.card

theorem mem_pairs {S : Finset ℤ} {k r i : ℕ} : (r,i) ∈ Pairs S k ↔
    1 ≤ r ∧ r ≤ k ∧ i+r < S.card := by
  constructor
  · intro h
    have hh := Finset.mem_filter.mp h
    have hp := Finset.mem_product.mp hh.1
    have hr := Finset.mem_Icc.mp hp.1
    exact ⟨hr.1, hr.2, hh.2⟩
  · rintro ⟨hr, hrk, hi⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨hr, hrk⟩, Finset.mem_range.mpr (by omega)⟩, hi⟩

def Inputs (S : Finset ℤ) (k : ℕ) : Finset (Σ _ : ℕ × ℕ, ℤ) :=
  (Pairs S k).sigma fun p => IntrinsicPoints S (point S p.2) (point S (p.2+p.1))

def code (S : Finset ℤ) (z : Σ _ : ℕ × ℕ, ℤ) : Σ _ : ℕ, ℤ × ℤ :=
  ⟨(point S (z.1.2+z.1.1)-point S z.1.2).toNat, (point S z.1.2,z.2)⟩

theorem code_injective {S : Finset ℤ} {k : ℕ} : Set.InjOn (code S) (Inputs S k) := by
  rintro ⟨⟨r,i⟩,x⟩ hz ⟨⟨s,j⟩,y⟩ hw he
  obtain ⟨hzp, _⟩ := Finset.mem_sigma.mp hz
  obtain ⟨hwp, _⟩ := Finset.mem_sigma.mp hw
  have hz' := mem_pairs.mp hzp
  have hw' := mem_pairs.mp hwp
  have hza : (0 : ℤ) < point S (i+r)-point S i := by
    have hh := point_strict (by omega : i < i+r) hz'.2.2
    omega
  have hwa : (0 : ℤ) < point S (j+s)-point S j := by
    have hh := point_strict (by omega : j < j+s) hw'.2.2
    omega
  have hstart := congrArg (fun p : Σ _ : ℕ, ℤ × ℤ => p.2.1) he
  have hthird := congrArg (fun p : Σ _ : ℕ, ℤ × ℤ => p.2.2) he
  have hgap := congrArg (fun p : Σ _ : ℕ, ℤ × ℤ => p.1) he
  change point S i = point S j at hstart
  change x = y at hthird
  change (point S (i+r)-point S i).toNat =
    (point S (j+s)-point S j).toNat at hgap
  have hgapZ := congrArg (fun n : ℕ => (n : ℤ)) hgap
  rw [Int.toNat_of_nonneg hza.le, Int.toNat_of_nonneg hwa.le] at hgapZ
  have hi := point_injective (by omega : i < S.card) (by omega : j < S.card) hstart
  have hj := point_injective hz'.2.2 hw'.2.2 (by omega :
    point S (i+r) = point S (j+s))
  have hri : (r,i) = (s,j) := Prod.ext (by omega) hi
  exact Sigma.ext hri (heq_of_eq hthird)

theorem code_mem_slots {N k : ℕ} {S : Finset ℤ} (hS : S ⊆ Ground N)
    {z : Σ _ : ℕ × ℕ, ℤ} (hz : z ∈ Inputs S k) :
    code S z ∈ NeighborSlots208.Slots N S := by
  rcases z with ⟨⟨r,i⟩,x⟩
  obtain ⟨hzp, hzx⟩ := Finset.mem_sigma.mp hz
  have hh := mem_pairs.mp hzp
  simpa only [code] using intrinsic_slot hS
    (point_mem (i := i) (by omega)) (point_mem (i := i+r) hh.2.2)
    (point_strict (i := i) (j := i+r) (by omega) hh.2.2) hzx

theorem input_mass_le {N k : ℕ} {S : Finset ℤ} (hS : S ⊆ Ground N) (u : ℝ) :
    (∑ z ∈ Inputs S k, TriangularWeights208.Weight u (code S z).1) ≤
      NeighborSlots208.Mass N u S := by
  have hsub : (Inputs S k).image (code S) ⊆ NeighborSlots208.Slots N S := by
    intro p hp
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hp
    exact code_mem_slots hS hz
  calc
    _ = ∑ p ∈ (Inputs S k).image (code S), TriangularWeights208.Weight u p.1 := by
      rw [Finset.sum_image code_injective]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun p _ _ => TriangularWeights208.weight_nonneg u p.1)

#print axioms actual_rank
#print axioms code_injective
#print axioms input_mass_le
end
end JSP233.RankSlots208
