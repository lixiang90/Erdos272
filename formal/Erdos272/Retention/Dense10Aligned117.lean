module

public import Erdos272.Retention.DenseAligned117
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Intervals

@[expose] public section

/-! A separate dense10 specialization, preserving the frozen first dense117
module.  This is used only after the actual minimum source exceeds N/10. -/
namespace JSP233.Dense10Aligned117
open StarCompletion APGeometry ThinFringe33 KKRetention32 Restore33
open scoped Classical BigOperators
noncomputable section

theorem dense_short_keys_card10 : (DenseAligned117.DenseShortKeys 10).card=32 := by
  norm_num [DenseAligned117.DenseShortKeys,Finset.card_sigma,Finset.sum_Icc_succ_top]

theorem actual_aligned_count32 {N M : ℕ} {E : Finset (Finset ℤ)} {L R : ℤ}
    (K : Finset ℤ→Relative13Fringe116.Key) (hlegal : Legal (Ground N) E)
    (hbad : ∀S∈E,¬IsAP S) (hdense : ∀S∈E,N<10*S.card)
    (hkeys : ∀S∈E,K S∈Relative13Fringe116.Keys)
    (hanchor : ∀S∈E,Relative13Fringe116.HasAnchor M L R (K S) S) :
    (E.filter (Relative13Fringe116.Aligned K M L)).card≤
      32*(Ground N\Finset.Icc L R).card := by
  simpa only [dense_short_keys_card10] using
    DenseAligned117.actual_aligned_count K hlegal hbad hdense hkeys hanchor

#print axioms dense_short_keys_card10
#print axioms actual_aligned_count32
end
end JSP233.Dense10Aligned117
