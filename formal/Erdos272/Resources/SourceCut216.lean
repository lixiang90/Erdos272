module

public import Erdos272.Arithmetic.Source240216
public import Erdos272.Resources.DeficiencyCuts208

@[expose] public section

namespace JSP233.SourceCut216
open StarCompletion APGeometry IntrinsicTriples208 SourceBridge208
open SourceCertified208 UnitNearAggregate208 SevenFamily208 Source240216
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def Height (i : ℕ) : ℕ := max i (max (eAt 240 i) (eAt 241 i))

def CheckHeight : Bool := (List.range 151).all fun i =>
  decide (i ≤ Height i ∧ Height i ≤ i+2)

theorem checked_height : CheckHeight = true := by decide +kernel

theorem height_bounds (i : ℕ) (hi : i ≤ 150) : i ≤ Height i ∧ Height i ≤ i + 2 := by
  exact of_decide_eq_true (List.all_eq_true.mp checked_height i
    (List.mem_range.mpr (by omega : i<151)))

theorem actual_pool_cut {S : Finset ℤ} {i : ℕ}
    (hsize : 240≤S.card) (hhi : S.card<2^50) (hi : i≤150)
    (hnear : ((Pool S).card : ℝ)<psi242 i) : Defect S<Height i := by
  by_contra hnot
  have hh : Height i≤Defect S := le_of_not_gt hnot
  have hf : floorAt row242 i≤(Pool S).card := by
    by_cases hbig : 242≤S.card
    · apply SourceCertified208.actual_source row242
      · change 242≤S.card
        exact hbig
      · exact hhi
      · exact (min_le_left i 184).trans ((le_max_left i _).trans hh)
    · have hs : S.card=240 ∨ S.card=241 := by omega
      have he : eAt S.card i≤Height i := by
        rcases hs with hs | hs
        · rw [hs]
          exact (le_max_left _ _).trans (le_max_right i _)
        · rw [hs]
          exact (le_max_right _ _).trans (le_max_right i _)
      exact (Source240216.physical_bound S.card hs i hi).trans
        (actual_source_of_defect (by omega : 2≤S.card) (he.trans hh))
  have hfR : (floorAt row242 i : ℝ)≤(Pool S).card := by exact_mod_cast hf
  change ((Pool S).card : ℝ)<(floorAt row242 i : ℝ) at hnear
  linarith only [hfR,hnear]

theorem actual_near_cut {A : Finset (Finset ℤ)} {S : Finset ℤ} {k : ℕ}
    (hS : S∈PoolNear A psi242 k) (hsize : 240≤S.card)
    (hhi : S.card<2^50) (hk : k<150) : Defect S<Height (k+1) :=
  actual_pool_cut hsize hhi (by omega) (Finset.mem_filter.mp hS).2

#print axioms checked_height
#print axioms height_bounds
#print axioms actual_pool_cut
#print axioms actual_near_cut
end JSP233.SourceCut216
