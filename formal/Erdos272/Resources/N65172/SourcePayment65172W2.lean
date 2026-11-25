module

public import Erdos272.Resources.N65968.SourcePayment65968W2

@[expose] public section

namespace JSP233.SourcePayment65172W2
open StarCompletion APGeometry NearAP36 SourceBridge208 IntrinsicTriples208 SevenFamily208 SourceScalars65968W2
open SourcePayment65968W2 (free_empty witness_link)
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

theorem actual_obligation {N : ℕ} {A F : Finset (Finset ℤ)} {A₀ : Finset ℤ}
    (hlo : 65172 ≤ N) (hhi : N ≤ 65967)
    (hlegal : Legal (Ground N) A) (hbad : ∀ S ∈ A, ¬IsAP S)
    (hsize : ∀ S ∈ A, 79 ≤ S.card) (hsparse : ∀ S ∈ A, 12*S.card ≤ N)
    (hlegalF : Legal (Ground N) F) (hAF : A ⊆ F) (hA₀ : A₀ ∈ F) (hW : A₀.card ≤ Witness) :
    UnitNearObligation N A G CoeffA CoeffB CoeffC := by
  refine ⟨Psi,21,psi_mono,psi_zero,reciprocal,?_⟩
  have hs : (∑ i ∈ Finset.range 21, (Psi (i+1)-Psi i)*((PoolNear A Psi i).card : ℝ)) ≤
      ∑ i ∈ Finset.range 21, (Psi (i+1)-Psi i)*Cost N i := by
    apply Finset.sum_le_sum
    intro i hi
    have hir := Finset.mem_range.mp hi
    by_cases he : i=0
    · subst i
      simp [SourcePayment65968W2.free_empty (by omega) hlegal hbad hsize,Cost]
    · have hit : i-1 < 20 := by omega
      have hl := links hit
      have hb := Layer65968.actual_upper (N:=N) (k:=52+(i-1)) (ell:=i) (psi:=Psi)
        (by omega) (by rw [hl.1]; omega) (by rw [hl.2.1]; omega)
        hlegal hbad (by simpa only [hl.2.2.1] using hsize) hsparse (by
          have hindex : i-1+2=i+1 := by omega
          dsimp only [Psi]
          rw [←hindex]
          exact_mod_cast hl.2.2.2) hlegalF hAF hA₀ (by
          rw [witness_link hit]
          exact hW)
      simp only [Cost,if_neg he]
      change _ ≤ (Psi (i+1)-Psi i)*ScalarUpper65968.Upper N (52+(i-1))
      exact mul_le_mul_of_nonneg_left hb (sub_nonneg.mpr (psi_mono (Nat.le_succ i)))
  have hp := mul_le_mul_of_nonneg_left hs (show 0 ≤ 6*G by have hh := g_positive; positivity)
  exact hp.trans_eq (fee N)
#print axioms actual_obligation

theorem actual_source {N : ℕ} {A F : Finset (Finset ℤ)} {A₀ : Finset ℤ}
    (hlo : 65172 ≤ N) (hhi : N ≤ 65967)
    (hlegal : Legal (Ground N) A) (hbad : ∀ S ∈ A, ¬IsAP S)
    (hsize : ∀ S ∈ A, 79 ≤ S.card) (hsparse : ∀ S ∈ A, 12*S.card ≤ N)
    (hlegalF : Legal (Ground N) F) (hAF : A ⊆ F) (hA₀ : A₀ ∈ F) (hW : A₀.card ≤ Witness) :
    (A.card : ℝ) ≤ 6*G*(∑ S ∈ F, ((Pool S).card : ℝ))+SourceUpper N := by
  have hb := WitnessSourcePayment80470.actual_source_of_obligation hlegalF hAF hA₀ hW g_positive.le
    (fun hLF hsub hA hcard => actual_obligation hlo hhi hlegal hbad hsize hsparse hLF hsub hA hcard)
  simpa only [SourceUpper,add_assoc] using hb
#print axioms actual_source

theorem actual_inner_source {N : ℕ} {A F : Finset (Finset ℤ)} {A₀ : Finset ℤ}
    (hlo : 65172 ≤ N) (hhi : N ≤ 65967)
    (hlegal : Legal (Ground N) A) (hbad : ∀ S ∈ A, ¬IsAP S)
    (hsize : ∀ S ∈ A, 79 ≤ S.card) (hsparse : ∀ S ∈ A, 12*S.card ≤ N)
    (hlegalF : Legal (Ground N) F) (hAF : A ⊆ F) (hA₀ : A₀ ∈ F) (hW : A₀.card ≤ Witness) :
    (A.card : ℝ) ≤ 6*G*(∑ S ∈ A, ((Pool S).card : ℝ))+SourceUpper N := by
  have ho := actual_obligation hlo hhi hlegal hbad hsize hsparse hlegalF hAF hA₀ hW
  have hb := SevenFamily208.actual_unit_source (A:=A) (F:=A) (le_refl A) g_positive.le ho
  simpa only [SourceUpper,add_assoc] using hb
#print axioms actual_inner_source
end
end JSP233.SourcePayment65172W2
