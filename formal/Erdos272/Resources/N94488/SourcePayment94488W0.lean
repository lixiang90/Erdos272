module

public import Erdos272.Resources.N94488.Layer94488
public import Erdos272.Resources.N94488.SourceData94488W0

@[expose] public section

namespace JSP233.SourcePayment94488W0
open StarCompletion APGeometry SevenFamily208 SourceData94488W0
open SourceBridge208 IntrinsicTriples208 CorrelatedSource109474 SourceQueryData94488
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def Cost (N i : ℕ) : ℝ := if i=0 then 0 else Layer94488.Upper N (0+(i-1))
def Weighted (N : ℕ) : ℝ := 6*G*(∑ i ∈ Finset.range 29, (Psi (i+1)-Psi i)*Cost N i)

theorem fee (N : ℕ) : Weighted N = SourceUpper N := by
  simp only [Weighted, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [G, Psi, potential, Cost, Layer94488.Upper, Layer94488.Slope, RowLightSlope94488.slope, CleanupRows94488.data,
    CleanupRows94488.data00, CleanupRows94488.data01, CleanupRows94488.data02, CleanupRows94488.data03, CleanupRows94488.data04, CleanupRows94488.data05, CleanupRows94488.data06, CleanupRows94488.data07, CleanupRows94488.data08, CleanupRows94488.data09, CleanupRows94488.data10, CleanupRows94488.data11, CleanupRows94488.data12, CleanupRows94488.data13, CleanupRows94488.data14, CleanupRows94488.data15, CleanupRows94488.data16, CleanupRows94488.data17, CleanupRows94488.data18, CleanupRows94488.data19, CleanupRows94488.data20, CleanupRows94488.data21, CleanupRows94488.data22, CleanupRows94488.data23, CleanupRows94488.data24, CleanupRows94488.data25, CleanupRows94488.data26, CleanupRows94488.data27, SourceUpper, CoeffA, CoeffB, CoeffC]
  ring

theorem free_empty {N : ℕ} {A : Finset (Finset ℤ)} (hhi : N ≤ 96560)
    (hlegal : Legal (Ground N) A) (hbad : ∀ S ∈ A, ¬IsAP S)
    (hsize : ∀ S ∈ A, 93 ≤ S.card) : PoolNear A Psi 0 = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro S hS
  obtain ⟨hSA, hnear⟩ := Finset.mem_filter.mp hS
  have hcard : 2 ≤ S.card := by have hh := hsize S hSA; omega
  have hb := SourceAtlas94488.actual_source (N := N) (S := S) (i := 0)
    (by decide) (by norm_num at *; omega) (hlegal.1 S hSA) hcard
    (by change 93 ≤ S.card; exact hsize S hSA)
    (by change 1 ≤ Defect S; exact MixedCore200000.crooked_defect_positive hcard (hbad S hSA))
  have hp : (2375 : ℕ) ≤ (Pool S).card := hb
  have hnearR : ((Pool S).card : ℝ) < (2375 : ℝ) := by
    simpa [Psi, potential] using hnear
  exact (not_le_of_gt hnearR) (by exact_mod_cast hp)

theorem actual_obligation {N : ℕ} {A : Finset (Finset ℤ)}
    (hlo : 94488 ≤ N) (hhi : N ≤ 96560)
    (hlegal : Legal (Ground N) A) (hbad : ∀ S ∈ A, ¬IsAP S)
    (hsize : ∀ S ∈ A, 93 ≤ S.card) (hsparse : ∀ S ∈ A, 12*S.card ≤ N) :
    UnitNearObligation N A G CoeffA CoeffB CoeffC := by
  refine ⟨Psi, 29, psi_mono, psi_zero, reciprocal, ?_⟩
  have hs : (∑ i ∈ Finset.range 29, (Psi (i+1)-Psi i)*((PoolNear A Psi i).card : ℝ)) ≤
      ∑ i ∈ Finset.range 29, (Psi (i+1)-Psi i)*Cost N i := by
    apply Finset.sum_le_sum
    intro i hi
    have hi8 := Finset.mem_range.mp hi
    by_cases he : i=0
    · subst i
      simp [free_empty hhi hlegal hbad hsize, Cost]
    · have hi7 : i-1 < 28 := by omega
      have hl := links hi7
      have hb := Layer94488.actual_upper (N := N) (k := 0+(i-1)) (ell := i) (psi := Psi)
        (by omega) (by simpa only [hl.1] using hlo) (by simpa only [hl.2.1] using hhi)
        hlegal hbad (by simpa only [hl.2.2.1] using hsize) hsparse (by
          have hindex : i-1+2 = i+1 := by omega
          dsimp only [Psi]
          rw [← hindex]
          exact_mod_cast hl.2.2.2)
      simp only [Cost, if_neg he]
      change _ ≤ (Psi (i+1)-Psi i)*Layer94488.Upper N (0+(i-1))
      exact mul_le_mul_of_nonneg_left hb (sub_nonneg.mpr (psi_mono (Nat.le_succ i)))
  have hp := mul_le_mul_of_nonneg_left hs (show 0 ≤ 6*G by have hh := g_positive; positivity)
  exact hp.trans_eq (fee N)

theorem actual_source {N : ℕ} {A F : Finset (Finset ℤ)}
    (hlo : 94488 ≤ N) (hhi : N ≤ 96560)
    (hlegal : Legal (Ground N) A) (hbad : ∀ S ∈ A, ¬IsAP S)
    (hsize : ∀ S ∈ A, 93 ≤ S.card) (hsparse : ∀ S ∈ A, 12*S.card ≤ N) (hAF : A ⊆ F) :
    (A.card : ℝ) ≤ 6*G*(∑ S ∈ F, ((Pool S).card : ℝ))+SourceUpper N := by
  have hb := SevenFamily208.actual_unit_source hAF g_positive.le (actual_obligation hlo hhi hlegal hbad hsize hsparse)
  simpa only [SourceUpper, add_assoc] using hb

#print axioms fee
#print axioms free_empty
#print axioms actual_obligation
#print axioms actual_source
end
end JSP233.SourcePayment94488W0
