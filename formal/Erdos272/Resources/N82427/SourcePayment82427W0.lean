module

public import Erdos272.Resources.N82427.Layer82427
public import Erdos272.Resources.N82427.SourceData82427W0

@[expose] public section

namespace JSP233.SourcePayment82427W0
open StarCompletion APGeometry SevenFamily208 SourceData82427W0
open SourceBridge208 IntrinsicTriples208
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def Cost (N i : ℕ) : ℝ := if i=0 then 0 else Layer82427.Upper N (0+(i-1))
def Weighted (N : ℕ) : ℝ := 6*G*(∑ i ∈ Finset.range 37, (Psi (i+1)-Psi i)*Cost N i)

theorem fee (N : ℕ) : Weighted N = SourceUpper N := by
  simp only [Weighted, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [G, Psi, potential, Cost, Layer82427.Upper, Layer82427.Slope, RowLightSlope82427.slope, RowLightSlope82427.cap, CleanupRows82427.data,
    CleanupRows82427.data00, CleanupRows82427.data01, CleanupRows82427.data02, CleanupRows82427.data03, CleanupRows82427.data04, CleanupRows82427.data05, CleanupRows82427.data06, CleanupRows82427.data07, CleanupRows82427.data08, CleanupRows82427.data09, CleanupRows82427.data10, CleanupRows82427.data11, CleanupRows82427.data12, CleanupRows82427.data13, CleanupRows82427.data14, CleanupRows82427.data15, CleanupRows82427.data16, CleanupRows82427.data17, CleanupRows82427.data18, CleanupRows82427.data19, CleanupRows82427.data20, CleanupRows82427.data21, CleanupRows82427.data22, CleanupRows82427.data23, CleanupRows82427.data24, CleanupRows82427.data25, CleanupRows82427.data26, CleanupRows82427.data27, CleanupRows82427.data28, CleanupRows82427.data29, CleanupRows82427.data30, CleanupRows82427.data31, CleanupRows82427.data32, CleanupRows82427.data33, CleanupRows82427.data34, CleanupRows82427.data35, SourceUpper, CoeffA, CoeffB, CoeffC]
  ring

theorem free_empty {N : ℕ} {A : Finset (Finset ℤ)} (hhi : N ≤ 83394)
    (hlegal : Legal (Ground N) A) (hbad : ∀ S ∈ A, ¬IsAP S)
    (hsize : ∀ S ∈ A, 87 ≤ S.card) : PoolNear A Psi 0 = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro S hS
  obtain ⟨hSA, hnear⟩ := Finset.mem_filter.mp hS
  have hcard : 2 ≤ S.card := by have hh := hsize S hSA; omega
  have hb := SourceAtlas82427.actual_source (N:=N) (S:=S) (i:=0)
    (by decide) (by norm_num at *; omega) (hlegal.1 S hSA) hcard
    (by change 87 ≤ S.card; exact hsize S hSA)
    (by change 1 ≤ Defect S; exact MixedCore200000.crooked_defect_positive hcard (hbad S hSA))
  have hp : (2240 : ℕ) ≤ (Pool S).card := hb
  have hnearR : ((Pool S).card : ℝ) < (2240 : ℝ) := by
    simpa [Psi, potential] using hnear
  exact (not_le_of_gt hnearR) (by exact_mod_cast hp)

theorem actual_obligation {N : ℕ} {A : Finset (Finset ℤ)}
    (hlo : 82427 ≤ N) (hhi : N ≤ 83394)
    (hlegal : Legal (Ground N) A) (hbad : ∀ S ∈ A, ¬IsAP S)
    (hsize : ∀ S ∈ A, 87 ≤ S.card) (hsparse : ∀ S ∈ A, 12*S.card ≤ N) :
    UnitNearObligation N A G CoeffA CoeffB CoeffC := by
  refine ⟨Psi, 37, psi_mono, psi_zero, reciprocal, ?_⟩
  have hs : (∑ i ∈ Finset.range 37, (Psi (i+1)-Psi i)*((PoolNear A Psi i).card : ℝ)) ≤
      ∑ i ∈ Finset.range 37, (Psi (i+1)-Psi i)*Cost N i := by
    apply Finset.sum_le_sum
    intro i hi
    have hi8 := Finset.mem_range.mp hi
    by_cases he : i=0
    · subst i
      simp [free_empty hhi hlegal hbad hsize, Cost]
    · have hi7 : i-1 < 36 := by omega
      have hl := links hi7
      have hb := Layer82427.actual_upper (N := N) (k := 0+(i-1)) (ell := i) (psi := Psi)
        (by omega) (by simpa only [hl.1] using hlo) (by simpa only [hl.2.1] using hhi)
        hlegal hbad (by simpa only [hl.2.2.1] using hsize) hsparse (by
          have hindex : i-1+2 = i+1 := by omega
          dsimp only [Psi]
          rw [← hindex]
          exact_mod_cast hl.2.2.2)
      simp only [Cost, if_neg he]
      change _ ≤ (Psi (i+1)-Psi i)*Layer82427.Upper N (0+(i-1))
      exact mul_le_mul_of_nonneg_left hb (sub_nonneg.mpr (psi_mono (Nat.le_succ i)))
  have hp := mul_le_mul_of_nonneg_left hs (show 0 ≤ 6*G by have hh := g_positive; positivity)
  exact hp.trans_eq (fee N)

theorem actual_source {N : ℕ} {A F : Finset (Finset ℤ)}
    (hlo : 82427 ≤ N) (hhi : N ≤ 83394)
    (hlegal : Legal (Ground N) A) (hbad : ∀ S ∈ A, ¬IsAP S)
    (hsize : ∀ S ∈ A, 87 ≤ S.card) (hsparse : ∀ S ∈ A, 12*S.card ≤ N) (hAF : A ⊆ F) :
    (A.card : ℝ) ≤ 6*G*(∑ S ∈ F, ((Pool S).card : ℝ))+SourceUpper N := by
  have hb := SevenFamily208.actual_unit_source hAF g_positive.le (actual_obligation hlo hhi hlegal hbad hsize hsparse)
  simpa only [SourceUpper, add_assoc] using hb

#print axioms fee
#print axioms free_empty
#print axioms actual_obligation
#print axioms actual_source
end
end JSP233.SourcePayment82427W0
