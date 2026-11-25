module

public import Erdos272.Counting.N86412.APReconstruction86412

@[expose] public section

namespace JSP233.APGaps86412
open ActualAPCount208 APInterval208 PureSource208 APBalanced86412 APReconstruction86412
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem initial_gap_nonincreasing {S A : Finset ℤ}
    (hA : IsInitial S A) (hb : BalancedTail S.card 2 A.card)
    (heq : (Codes S 2).card=intervalMultiplicity S.card 2)
    {u v w : ℤ} (hu : u∈A) (hv : v∈A) (hw : w∈A)
    (huv : u<v) (hvw : v<w)
    (hgap : ∀ z∈A, v<z → z<w → False) : w-v≤v-u := by
  have hz := initial_pair_end (by decide : 2≤2) hA hb heq hu hv huv
  change u+2*(v-u)∈S at hz
  by_contra hh
  have hzw : u+2*(v-u)<w := by omega
  have hzA := hA.2 _ hz _ hw hzw.le
  exact hgap _ hzA (by omega) hzw

theorem tail_gap_nondecreasing {S T : Finset ℤ}
    (hT : IsInitial S T) (hb : BalancedTail S.card 2 (S\T).card)
    (heq : (Codes S 2).card=intervalMultiplicity S.card 2)
    {u v w : ℤ} (hu : u∈S\T) (hv : v∈S\T) (hw : w∈S\T)
    (huv : u<v) (hvw : v<w)
    (hgap : ∀ z∈S\T, u<z → z<v → False) : v-u≤w-v := by
  have hz := tail_pair_start (by decide : 2≤2) hT hb heq hv hw hvw
  change w-2*(w-v)∈S at hz
  by_contra hh
  have huz : u<w-2*(w-v) := by omega
  have hzt : w-2*(w-v)∉T := by
    intro hmem
    exact (Finset.mem_sdiff.mp hu).2
      (hT.2 u (Finset.mem_sdiff.mp hu).1 _ hmem huz.le)
  exact hgap _ (Finset.mem_sdiff.mpr ⟨hz, hzt⟩) huz (by omega)

#print axioms initial_gap_nonincreasing
#print axioms tail_gap_nondecreasing
end
end JSP233.APGaps86412
