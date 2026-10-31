import Erdos272.Resources.PairRanks208
import Erdos272.Resources.NeighborSlots208

/-! Genuine intrinsic third-point supplies for the first three rank distances.
All AP covers inside the actual source are excluded, rather than only
three-term APs on the three displayed points. -/
namespace JSP233.NeighborSupply208
open StarCompletion APGeometry SourceBridge208 IntrinsicTriples208
open PairEnvelope208 PairRanks208
open scoped Classical
noncomputable section
set_option maxHeartbeats 0

theorem covered_subset (S : Finset ℤ) (a b : ℤ) : CoveredPoints S a b ⊆ S :=
  Finset.filter_subset _ _

theorem intrinsic_partition (S : Finset ℤ) (a b : ℤ) :
    (IntrinsicPoints S a b).card + (CoveredPoints S a b).card = S.card := by
  have h := Finset.card_sdiff_add_card_inter S (CoveredPoints S a b)
  rw [Finset.inter_eq_right.mpr (covered_subset S a b)] at h
  exact h

theorem coarse_card {S : Finset ℤ} {a b : ℤ}
    (ha : a ∈ S) (hb : b ∈ S) (hab : a < b) :
    (Envelope S (b-a) a b).card ≤ MaxAPSize S := by
  apply envelope_card_le_max (R := {a,b}) _ (pair_APAt hab) (by simp) (by simp)
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl <;> assumption

theorem union_card (U V : Finset ℤ) : (U ∪ V).card = U.card + (V \ U).card := by
  have h := Finset.card_union_add_card_inter U V
  have h' := Finset.card_sdiff_add_card_inter V U
  rw [Finset.inter_comm V U] at h'
  omega

theorem rank_one_supply {S : Finset ℤ} {a b : ℤ}
    (ha : a ∈ S) (hb : b ∈ S) (hab : a < b) (hrank : Rank S a b ≤ 1) :
    Defect S ≤ (IntrinsicPoints S a b).card := by
  have hcov := Finset.card_le_card (covered_rank_one hab hrank)
  have hmax := coarse_card ha hb hab
  have hpart := intrinsic_partition S a b
  unfold Defect
  omega

theorem rank_two_supply {S : Finset ℤ} {a b : ℤ}
    (ha : a ∈ S) (hb : b ∈ S) (hab : a < b) (hrank : Rank S a b ≤ 2) :
    Defect S - (MaxAPSize S-MaxAPSize S/2) ≤ (IntrinsicPoints S a b).card := by
  have hcov := Finset.card_le_card (covered_rank_two hab hrank)
  rw [union_card] at hcov
  have hmax := coarse_card ha hb hab
  have hextra := level_extra S hab (by decide : 0 < 2)
  have hpart := intrinsic_partition S a b
  unfold Defect
  omega

theorem rank_three_supply {S : Finset ℤ} {a b : ℤ}
    (ha : a ∈ S) (hb : b ∈ S) (hab : a < b) (hrank : Rank S a b ≤ 3) :
    Defect S - (MaxAPSize S-MaxAPSize S/3) ≤ (IntrinsicPoints S a b).card := by
  obtain ⟨q, hq, hsub⟩ := covered_rank_three hab hrank
  have hqcases : q=2 ∨ q=3 := by simpa only [Finset.mem_insert, Finset.mem_singleton] using hq
  have hcov := Finset.card_le_card hsub
  rw [union_card] at hcov
  have hmax := coarse_card ha hb hab
  have hextra := level_extra S hab (by omega : 0 < q)
  have hpart := intrinsic_partition S a b
  unfold Defect
  rcases hqcases with rfl | rfl <;> omega

theorem rank_two_supply_floor {S : Finset ℤ} {a b : ℤ}
    (ha : a ∈ S) (hb : b ∈ S) (hab : a < b) (hrank : Rank S a b ≤ 2) :
    (3*Defect S-S.card)/2 ≤ (IntrinsicPoints S a b).card := by
  have h := rank_two_supply ha hb hab hrank
  have hmax := maxAPSize_le_card S
  unfold Defect at *
  omega

theorem rank_three_supply_floor {S : Finset ℤ} {a b : ℤ}
    (ha : a ∈ S) (hb : b ∈ S) (hab : a < b) (hrank : Rank S a b ≤ 3) :
    (5*Defect S-2*S.card)/3 ≤ (IntrinsicPoints S a b).card := by
  have h := rank_three_supply ha hb hab hrank
  have hmax := maxAPSize_le_card S
  unfold Defect at *
  omega

theorem endpoint_covered {S : Finset ℤ} {a b : ℤ} (ha : a ∈ S) (hb : b ∈ S) :
    a ∈ CoveredPoints S a b ∧ b ∈ CoveredPoints S a b := by
  have hsub : ({a,b} : Finset ℤ) ⊆ S := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  constructor
  · exact Finset.mem_filter.mpr ⟨ha, {a,b}, pair_isAP a b, hsub, by simp, by simp, by simp⟩
  · exact Finset.mem_filter.mpr ⟨hb, {a,b}, pair_isAP a b, hsub, by simp, by simp, by simp⟩

theorem intrinsic_triple {S : Finset ℤ} {a b x : ℤ}
    (ha : a ∈ S) (hb : b ∈ S) (hab : a < b) (hx : x ∈ IntrinsicPoints S a b) :
    ({a,b,x} : Finset ℤ) ∈ Pool S := by
  have hxS := (Finset.mem_sdiff.mp hx).1
  have hno := (Finset.mem_sdiff.mp hx).2
  have hep := endpoint_covered ha hb
  have hxa : x ≠ a := by intro he; exact hno (he ▸ hep.1)
  have hxb : x ≠ b := by intro he; exact hno (he ▸ hep.2)
  apply mem_pool.mpr
  refine ⟨?_, ?_, ?_⟩
  · intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl <;> assumption
  · rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨by omega, Ne.symm hxa⟩), Finset.card_pair (Ne.symm hxb)]
  · rintro ⟨R, hR, hQR, hRS⟩
    apply hno
    exact Finset.mem_filter.mpr ⟨hxS, R, hR, hRS,
      hQR (by simp), hQR (by simp), hQR (by simp)⟩

theorem intrinsic_slot {N : ℕ} {S : Finset ℤ} {a b x : ℤ}
    (hS : S ⊆ Ground N) (ha : a ∈ S) (hb : b ∈ S) (hab : a < b)
    (hx : x ∈ IntrinsicPoints S a b) :
    (⟨(b-a).toNat, (a,x)⟩ : Σ _ : ℕ, ℤ × ℤ) ∈ NeighborSlots208.Slots N S := by
  have hD : ((b-a).toNat : ℤ) = b-a := Int.toNat_of_nonneg (by omega)
  have haB := (mem_ground N a).mp (hS ha)
  have hbB := (mem_ground N b).mp (hS hb)
  apply Finset.mem_sigma.mpr
  refine ⟨?_, ?_⟩
  · change (b-a).toNat ∈ Finset.Icc 1 (N-1)
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_product.mpr ⟨ha, (Finset.mem_sdiff.mp hx).1⟩, ?_, ?_⟩
  · simpa only [hD, add_sub_cancel] using hb
  · simpa only [hD, add_sub_cancel] using intrinsic_triple ha hb hab hx

#print axioms rank_one_supply
#print axioms rank_two_supply
#print axioms rank_three_supply
#print axioms intrinsic_triple
#print axioms intrinsic_slot
end
end JSP233.NeighborSupply208
