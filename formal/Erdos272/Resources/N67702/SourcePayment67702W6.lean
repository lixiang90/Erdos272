module

public import Erdos272.Resources.N67702.Layer67702
public import Erdos272.Resources.N67702.SourceAtlas67702
public import Erdos272.Resources.N67702.SourceData67702W6
public import Erdos272.Resources.N80470.WitnessSourcePayment80470

@[expose] public section

namespace JSP233.SourcePayment67702W6
open StarCompletion APGeometry NearAP36 SourceBridge208 IntrinsicTriples208 SevenFamily208 SourceData67702W6
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

def Cost (N i : ℕ) : ℝ := if i=0 then 0 else Layer67702.Upper N (116+(i-1))
def Weighted (N : ℕ) : ℝ := 6*G*(∑ i ∈ Finset.range 13, (Psi (i+1)-Psi i)*Cost N i)

theorem fee (N : ℕ) : Weighted N=SourceUpper N := by
  simp only [Weighted,Finset.sum_range_succ,Finset.sum_range_zero]
  norm_num [G, Psi, potential, Cost, Layer67702.Upper, WitnessActualLayer80470.Upper, WitnessHighNumeric67702.data, CleanupRows67702.data, WitnessHighNumeric67702.data116, WitnessHighNumeric67702.data117, WitnessHighNumeric67702.data118, WitnessHighNumeric67702.data119, WitnessHighNumeric67702.data120, WitnessHighNumeric67702.data121, WitnessHighNumeric67702.data122, WitnessHighNumeric67702.data123, WitnessHighNumeric67702.data124, WitnessHighNumeric67702.data125, WitnessHighNumeric67702.data126, WitnessHighNumeric67702.data127, CleanupRows67702.data116, CleanupRows67702.data117, CleanupRows67702.data118, CleanupRows67702.data119, CleanupRows67702.data120, CleanupRows67702.data121, CleanupRows67702.data122, CleanupRows67702.data123, CleanupRows67702.data124, CleanupRows67702.data125, CleanupRows67702.data126, CleanupRows67702.data127, SourceUpper, CoeffA, CoeffB, CoeffC]
  ring
#print axioms fee

theorem witness_link {i : ℕ} (hi : i < 12) :
    Layer67702.Witness (116+i)=Witness := by
  interval_cases i <;> rfl
#print axioms witness_link

theorem free_empty {N : ℕ} {A : Finset (Finset ℤ)} (hhi : N ≤ 76708)
    (hlegal : Legal (Ground N) A) (hbad : ∀ S ∈ A, ¬IsAP S)
    (hsize : ∀ S ∈ A, 83 ≤ S.card) : PoolNear A Psi 0=∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro S hS
  obtain ⟨hSA,hnear⟩ := Finset.mem_filter.mp hS
  have hcard : 2 ≤ S.card := by have hh := hsize S hSA; omega
  have hb := SourceAtlas67702.actual_source (N:=N) (S:=S) (i:=254)
    (by decide) (by norm_num at *; omega) (hlegal.1 S hSA) hcard
    (by change 83 ≤ S.card; exact hsize S hSA)
    (by change 1 ≤ Defect S; exact MixedCore200000.crooked_defect_positive hcard (hbad S hSA))
  have hp : (2058 : ℕ) ≤ (Pool S).card := hb
  have hn : ((Pool S).card : ℝ) < (2058 : ℝ) := by
    simpa [Psi,potential] using hnear
  exact (not_le_of_gt hn) (by exact_mod_cast hp)
#print axioms free_empty

theorem actual_obligation {N : ℕ} {A F : Finset (Finset ℤ)} {A₀ : Finset ℤ}
    (hlo : 67702 ≤ N) (hhi : N ≤ 76708)
    (hlegal : Legal (Ground N) A) (hbad : ∀ S ∈ A, ¬IsAP S)
    (hsize : ∀ S ∈ A, 83 ≤ S.card) (hsparse : ∀ S ∈ A, 12*S.card ≤ N)
    (hlegalF : Legal (Ground N) F) (hAF : A ⊆ F) (hA₀ : A₀ ∈ F) (hW : A₀.card ≤ Witness) :
    UnitNearObligation N A G CoeffA CoeffB CoeffC := by
  refine ⟨Psi,13,psi_mono,psi_zero,reciprocal,?_⟩
  have hs : (∑ i ∈ Finset.range 13, (Psi (i+1)-Psi i)*((PoolNear A Psi i).card : ℝ)) ≤
      ∑ i ∈ Finset.range 13, (Psi (i+1)-Psi i)*Cost N i := by
    apply Finset.sum_le_sum
    intro i hi
    have hir := Finset.mem_range.mp hi
    by_cases he : i=0
    · subst i
      simp [free_empty hhi hlegal hbad hsize,Cost]
    · have hit : i-1 < 12 := by omega
      have hl := links hit
      have hb := Layer67702.actual_upper (N:=N) (k:=116+(i-1)) (ell:=i) (psi:=Psi)
        (by omega) (by simpa only [hl.1] using hlo) (by simpa only [hl.2.1] using hhi)
        hlegal hbad (by simpa only [hl.2.2.1] using hsize) hsparse (by
          have hindex : i-1+2=i+1 := by omega
          dsimp only [Psi]
          rw [←hindex]
          exact_mod_cast hl.2.2.2) hlegalF hAF hA₀ (by
          rw [witness_link hit]
          exact hW)
      simp only [Cost,if_neg he]
      change _ ≤ (Psi (i+1)-Psi i)*Layer67702.Upper N (116+(i-1))
      exact mul_le_mul_of_nonneg_left hb (sub_nonneg.mpr (psi_mono (Nat.le_succ i)))
  have hp := mul_le_mul_of_nonneg_left hs (show 0 ≤ 6*G by have hh := g_positive; positivity)
  exact hp.trans_eq (fee N)
#print axioms actual_obligation

theorem actual_source {N : ℕ} {A F : Finset (Finset ℤ)} {A₀ : Finset ℤ}
    (hlo : 67702 ≤ N) (hhi : N ≤ 76708)
    (hlegal : Legal (Ground N) A) (hbad : ∀ S ∈ A, ¬IsAP S)
    (hsize : ∀ S ∈ A, 83 ≤ S.card) (hsparse : ∀ S ∈ A, 12*S.card ≤ N)
    (hlegalF : Legal (Ground N) F) (hAF : A ⊆ F) (hA₀ : A₀ ∈ F) (hW : A₀.card ≤ Witness) :
    (A.card : ℝ) ≤ 6*G*(∑ S ∈ F, ((Pool S).card : ℝ))+SourceUpper N := by
  have hb := WitnessSourcePayment80470.actual_source_of_obligation hlegalF hAF hA₀ hW g_positive.le
    (fun hLF hsub hA hcard => actual_obligation hlo hhi hlegal hbad hsize hsparse hLF hsub hA hcard)
  simpa only [SourceUpper,add_assoc] using hb
#print axioms actual_source

theorem actual_inner_source {N : ℕ} {A F : Finset (Finset ℤ)} {A₀ : Finset ℤ}
    (hlo : 67702 ≤ N) (hhi : N ≤ 76708)
    (hlegal : Legal (Ground N) A) (hbad : ∀ S ∈ A, ¬IsAP S)
    (hsize : ∀ S ∈ A, 83 ≤ S.card) (hsparse : ∀ S ∈ A, 12*S.card ≤ N)
    (hlegalF : Legal (Ground N) F) (hAF : A ⊆ F) (hA₀ : A₀ ∈ F) (hW : A₀.card ≤ Witness) :
    (A.card : ℝ) ≤ 6*G*(∑ S ∈ A, ((Pool S).card : ℝ))+SourceUpper N := by
  have ho := actual_obligation hlo hhi hlegal hbad hsize hsparse hlegalF hAF hA₀ hW
  have hb := SevenFamily208.actual_unit_source (A:=A) (F:=A) (le_refl A) g_positive.le ho
  simpa only [SourceUpper,add_assoc] using hb
#print axioms actual_inner_source
end
end JSP233.SourcePayment67702W6
