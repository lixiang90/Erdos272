import Erdos272.Geometry.BlockAP119

/-! Every actual finite trace loses at most720 points near its own extrema.
Its remaining actual points sit in blocks wholly inside its own span. The
ceil-block cover explicitly pays the final partial block. -/
namespace JSP233.BlockPacking119
open StarCompletion APGeometry BlockAP119
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

def Middle (S : Finset ℤ) (lo hi : ℤ) : Finset ℤ :=
  S\(Finset.Icc lo (lo+359)∪Finset.Icc (hi-359) hi)

def Active (lo hi A : ℤ) : Prop := lo≤A ∧ A+359≤hi

theorem actual_middle_card_payment (S : Finset ℤ) (lo hi : ℤ) :
    S.card≤(Middle S lo hi).card+720 := by
  let B := Finset.Icc lo (lo+359)∪Finset.Icc (hi-359) hi
  have hc := Finset.card_sdiff_add_card_inter S B
  have hu := Finset.card_union_le (Finset.Icc lo (lo+359)) (Finset.Icc (hi-359) hi)
  have hb := Finset.card_le_card (Finset.inter_subset_right (s₁:=S) (s₂:=B))
  change B.card≤(Finset.Icc lo (lo+359)).card+(Finset.Icc (hi-359) hi).card at hu
  have h1 : (Finset.Icc lo (lo+359)).card=360 := by simp only [Int.card_Icc];omega
  have h2 : (Finset.Icc (hi-359) hi).card=360 := by simp only [Int.card_Icc];omega
  change (S\B).card+(S∩B).card=S.card at hc
  change S.card≤(S\B).card+720
  omega

theorem actual_middle_block_active {S : Finset ℤ} {lo hi A z : ℤ}
    (hspan : ∀x∈S,lo≤x ∧ x≤hi)
    (hz : z∈Middle S lo hi) (hzB : z∈Block A) : Active lo hi A := by
  obtain ⟨hzS,hznot⟩ := Finset.mem_sdiff.mp hz
  have hzspan := hspan z hzS
  have hzI := Finset.mem_Icc.mp hzB
  have hn1 : z∉Finset.Icc lo (lo+359) := by
    intro hh;exact hznot (Finset.mem_union_left _ hh)
  have hn2 : z∉Finset.Icc (hi-359) hi := by
    intro hh;exact hznot (Finset.mem_union_right _ hh)
  simp only [Finset.mem_Icc,not_and] at hn1 hn2
  dsimp only [Active]
  constructor <;> omega

theorem actual_interval_block_cover {L z : ℤ} {M : ℕ}
    (hz : z∈Finset.Icc L (L+(M:ℤ)-1)) :
    ∃j∈Finset.range ((M+359)/360),z∈Block (L+360*(j:ℤ)) := by
  have hzi := Finset.mem_Icc.mp hz
  let j := ((z-L)/360).toNat
  have hjcast : (j:ℤ)=(z-L)/360 := Int.toNat_of_nonneg (by omega)
  have hdiv := Int.emod_add_mul_ediv (z-L) 360
  have hr0 := Int.emod_nonneg (z-L) (by norm_num : (360:ℤ)≠0)
  have hrU := Int.emod_lt_of_pos (z-L) (by norm_num : (0:ℤ)<360)
  have hjbound : j<(M+359)/360 := by omega
  refine ⟨j,Finset.mem_range.mpr hjbound,?_⟩
  exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩

theorem actual_middle_block_cover {S : Finset ℤ} {L lo hi : ℤ} {M : ℕ}
    (hS : S⊆Finset.Icc L (L+(M:ℤ)-1))
    (hspan : ∀x∈S,lo≤x ∧ x≤hi) :
    Middle S lo hi⊆(Finset.range ((M+359)/360)).biUnion (fun j=>
      if Active lo hi (L+360*(j:ℤ)) then S∩Block (L+360*(j:ℤ)) else ∅) := by
  intro z hz
  have hzS := (Finset.mem_sdiff.mp hz).1
  obtain ⟨j,hj,hzB⟩ := actual_interval_block_cover (hS hzS)
  have ha := actual_middle_block_active hspan hz hzB
  apply Finset.mem_biUnion.mpr
  refine ⟨j,hj,?_⟩
  rw [if_pos ha]
  exact Finset.mem_inter.mpr ⟨hzS,hzB⟩

theorem actual_trace_sum_bound {F : Finset (Finset ℤ)}
    (T : Finset ℤ→Finset ℤ) (lo hi : Finset ℤ→ℤ) (L : ℤ) (M K : ℕ)
    (hsub : ∀S∈F,T S⊆Finset.Icc L (L+(M:ℤ)-1))
    (hspan : ∀S∈F,∀x∈T S,lo S≤x ∧ x≤hi S)
    (hblock : ∀A:ℤ,(∑S∈F.filter (fun S=>Active (lo S) (hi S) A),
      ((T S)∩Block A).card)≤K) :
    (∑S∈F,(T S).card)≤K*((M+359)/360)+720*F.card := by
  let J := Finset.range ((M+359)/360)
  let P := fun (j:ℕ) (S:Finset ℤ)=>
    if Active (lo S) (hi S) (L+360*(j:ℤ)) then (T S)∩Block (L+360*(j:ℤ)) else ∅
  have hcover : ∀S∈F,(Middle (T S) (lo S) (hi S)).card≤∑j∈J,(P j S).card := by
    intro S hS
    have hc := Finset.card_le_card (actual_middle_block_cover (hsub S hS) (hspan S hS))
    have hb := Finset.card_biUnion_le (s:=J) (t:=fun j=>P j S)
    exact hc.trans hb
  have hpoint : ∀S∈F,(T S).card≤(∑j∈J,(P j S).card)+720 := by
    intro S hS
    have hp := actual_middle_card_payment (T S) (lo S) (hi S)
    exact hp.trans (Nat.add_le_add_right (hcover S hS) 720)
  have hs := Finset.sum_le_sum hpoint
  have hlocal : ∀j∈J,(∑S∈F,(P j S).card)≤K := by
    intro j _hj
    have he : (∑S∈F,(P j S).card)=
        ∑S∈F.filter (fun S=>Active (lo S) (hi S) (L+360*(j:ℤ))),
          ((T S)∩Block (L+360*(j:ℤ))).card := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro S _hS
      dsimp only [P]
      split_ifs <;> simp
    rw [he]
    exact hblock _
  have hb := Finset.sum_le_sum hlocal
  rw [Finset.sum_add_distrib] at hs
  rw [Finset.sum_comm] at hs
  have hs' : (∑S∈F,(T S).card)≤(∑j∈J,∑S∈F,(P j S).card)+720*F.card := by
    simpa [Nat.mul_comm] using hs
  have hb' : (∑j∈J,∑S∈F,(P j S).card)≤K*((M+359)/360) := by
    simpa [J,Nat.mul_comm] using hb
  exact hs'.trans (Nat.add_le_add_right hb' (720*F.card))

#print axioms actual_middle_card_payment
#print axioms actual_middle_block_active
#print axioms actual_interval_block_cover
#print axioms actual_middle_block_cover
#print axioms actual_trace_sum_bound
end
end JSP233.BlockPacking119
