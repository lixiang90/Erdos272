module

public import Erdos272.Resources.N67702.Layer67702
public import Erdos272.Resources.N67702.SourceAtlas67702
public import Erdos272.Resources.N67702.SourceData67702W1
public import Erdos272.Resources.N80470.WitnessSourcePayment80470

@[expose] public section

namespace JSP233.SourcePayment67702W1
open StarCompletion APGeometry NearAP36 SourceBridge208 IntrinsicTriples208 SevenFamily208 SourceData67702W1
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

def Cost (N i : ℕ) : ℝ := if i=0 then 0 else Layer67702.Upper N (20+(i-1))
def Weighted (N : ℕ) : ℝ := 6*G*(∑ i ∈ Finset.range 29, (Psi (i+1)-Psi i)*Cost N i)

theorem fee (N : ℕ) : Weighted N=SourceUpper N := by
  simp only [Weighted,Finset.sum_range_succ,Finset.sum_range_zero]
  norm_num [G, Psi, potential, Cost, Layer67702.Upper, WitnessActualLayer80470.Upper, WitnessHighNumeric67702.data, CleanupRows67702.data, WitnessHighNumeric67702.data020, WitnessHighNumeric67702.data021, WitnessHighNumeric67702.data022, WitnessHighNumeric67702.data023, WitnessHighNumeric67702.data024, WitnessHighNumeric67702.data025, WitnessHighNumeric67702.data026, WitnessHighNumeric67702.data027, WitnessHighNumeric67702.data028, WitnessHighNumeric67702.data029, WitnessHighNumeric67702.data030, WitnessHighNumeric67702.data031, WitnessHighNumeric67702.data032, WitnessHighNumeric67702.data033, WitnessHighNumeric67702.data034, WitnessHighNumeric67702.data035, WitnessHighNumeric67702.data036, WitnessHighNumeric67702.data037, WitnessHighNumeric67702.data038, WitnessHighNumeric67702.data039, WitnessHighNumeric67702.data040, WitnessHighNumeric67702.data041, WitnessHighNumeric67702.data042, WitnessHighNumeric67702.data043, WitnessHighNumeric67702.data044, WitnessHighNumeric67702.data045, WitnessHighNumeric67702.data046, WitnessHighNumeric67702.data047, CleanupRows67702.data20, CleanupRows67702.data21, CleanupRows67702.data22, CleanupRows67702.data23, CleanupRows67702.data24, CleanupRows67702.data25, CleanupRows67702.data26, CleanupRows67702.data27, CleanupRows67702.data28, CleanupRows67702.data29, CleanupRows67702.data30, CleanupRows67702.data31, CleanupRows67702.data32, CleanupRows67702.data33, CleanupRows67702.data34, CleanupRows67702.data35, CleanupRows67702.data36, CleanupRows67702.data37, CleanupRows67702.data38, CleanupRows67702.data39, CleanupRows67702.data40, CleanupRows67702.data41, CleanupRows67702.data42, CleanupRows67702.data43, CleanupRows67702.data44, CleanupRows67702.data45, CleanupRows67702.data46, CleanupRows67702.data47, SourceUpper, CoeffA, CoeffB, CoeffC]
  ring
#print axioms fee

theorem witness_link {i : ℕ} (hi : i < 28) :
    Layer67702.Witness (20+i)=Witness := by
  interval_cases i <;> rfl
#print axioms witness_link

theorem free_empty {N : ℕ} {A : Finset (Finset ℤ)} (hhi : N ≤ 69457)
    (hlegal : Legal (Ground N) A) (hbad : ∀ S ∈ A, ¬IsAP S)
    (hsize : ∀ S ∈ A, 79 ≤ S.card) : PoolNear A Psi 0=∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro S hS
  obtain ⟨hSA,hnear⟩ := Finset.mem_filter.mp hS
  have hcard : 2 ≤ S.card := by have hh := hsize S hSA; omega
  have hb := SourceAtlas67702.actual_source (N:=N) (S:=S) (i:=54)
    (by decide) (by norm_num at *; omega) (hlegal.1 S hSA) hcard
    (by change 79 ≤ S.card; exact hsize S hSA)
    (by change 1 ≤ Defect S; exact MixedCore200000.crooked_defect_positive hcard (hbad S hSA))
  have hp : (1854 : ℕ) ≤ (Pool S).card := hb
  have hn : ((Pool S).card : ℝ) < (1854 : ℝ) := by
    simpa [Psi,potential] using hnear
  exact (not_le_of_gt hn) (by exact_mod_cast hp)
#print axioms free_empty

theorem actual_obligation {N : ℕ} {A F : Finset (Finset ℤ)} {A₀ : Finset ℤ}
    (hlo : 67702 ≤ N) (hhi : N ≤ 69457)
    (hlegal : Legal (Ground N) A) (hbad : ∀ S ∈ A, ¬IsAP S)
    (hsize : ∀ S ∈ A, 79 ≤ S.card) (hsparse : ∀ S ∈ A, 12*S.card ≤ N)
    (hlegalF : Legal (Ground N) F) (hAF : A ⊆ F) (hA₀ : A₀ ∈ F) (hW : A₀.card ≤ Witness) :
    UnitNearObligation N A G CoeffA CoeffB CoeffC := by
  refine ⟨Psi,29,psi_mono,psi_zero,reciprocal,?_⟩
  have hs : (∑ i ∈ Finset.range 29, (Psi (i+1)-Psi i)*((PoolNear A Psi i).card : ℝ)) ≤
      ∑ i ∈ Finset.range 29, (Psi (i+1)-Psi i)*Cost N i := by
    apply Finset.sum_le_sum
    intro i hi
    have hir := Finset.mem_range.mp hi
    by_cases he : i=0
    · subst i
      simp [free_empty hhi hlegal hbad hsize,Cost]
    · have hit : i-1 < 28 := by omega
      have hl := links hit
      have hb := Layer67702.actual_upper (N:=N) (k:=20+(i-1)) (ell:=i) (psi:=Psi)
        (by omega) (by simpa only [hl.1] using hlo) (by simpa only [hl.2.1] using hhi)
        hlegal hbad (by simpa only [hl.2.2.1] using hsize) hsparse (by
          have hindex : i-1+2=i+1 := by omega
          dsimp only [Psi]
          rw [←hindex]
          exact_mod_cast hl.2.2.2) hlegalF hAF hA₀ (by
          rw [witness_link hit]
          exact hW)
      simp only [Cost,if_neg he]
      change _ ≤ (Psi (i+1)-Psi i)*Layer67702.Upper N (20+(i-1))
      exact mul_le_mul_of_nonneg_left hb (sub_nonneg.mpr (psi_mono (Nat.le_succ i)))
  have hp := mul_le_mul_of_nonneg_left hs (show 0 ≤ 6*G by have hh := g_positive; positivity)
  exact hp.trans_eq (fee N)
#print axioms actual_obligation

theorem actual_source {N : ℕ} {A F : Finset (Finset ℤ)} {A₀ : Finset ℤ}
    (hlo : 67702 ≤ N) (hhi : N ≤ 69457)
    (hlegal : Legal (Ground N) A) (hbad : ∀ S ∈ A, ¬IsAP S)
    (hsize : ∀ S ∈ A, 79 ≤ S.card) (hsparse : ∀ S ∈ A, 12*S.card ≤ N)
    (hlegalF : Legal (Ground N) F) (hAF : A ⊆ F) (hA₀ : A₀ ∈ F) (hW : A₀.card ≤ Witness) :
    (A.card : ℝ) ≤ 6*G*(∑ S ∈ F, ((Pool S).card : ℝ))+SourceUpper N := by
  have hb := WitnessSourcePayment80470.actual_source_of_obligation hlegalF hAF hA₀ hW g_positive.le
    (fun hLF hsub hA hcard => actual_obligation hlo hhi hlegal hbad hsize hsparse hLF hsub hA hcard)
  simpa only [SourceUpper,add_assoc] using hb
#print axioms actual_source

theorem actual_inner_source {N : ℕ} {A F : Finset (Finset ℤ)} {A₀ : Finset ℤ}
    (hlo : 67702 ≤ N) (hhi : N ≤ 69457)
    (hlegal : Legal (Ground N) A) (hbad : ∀ S ∈ A, ¬IsAP S)
    (hsize : ∀ S ∈ A, 79 ≤ S.card) (hsparse : ∀ S ∈ A, 12*S.card ≤ N)
    (hlegalF : Legal (Ground N) F) (hAF : A ⊆ F) (hA₀ : A₀ ∈ F) (hW : A₀.card ≤ Witness) :
    (A.card : ℝ) ≤ 6*G*(∑ S ∈ A, ((Pool S).card : ℝ))+SourceUpper N := by
  have ho := actual_obligation hlo hhi hlegal hbad hsize hsparse hlegalF hAF hA₀ hW
  have hb := SevenFamily208.actual_unit_source (A:=A) (F:=A) (le_refl A) g_positive.le ho
  simpa only [SourceUpper,add_assoc] using hb
#print axioms actual_inner_source
end
end JSP233.SourcePayment67702W1
