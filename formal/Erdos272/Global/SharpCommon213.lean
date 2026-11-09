module

public import Erdos272.Global.PaddedCommon212
public import Erdos272.Resources.SharpSmall212
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

namespace JSP233.SharpCommon213
open StarCompletion APGeometry DenseDeletion40 Density41 SparseSmall39
open PrivateFinset IntrinsicTriples208 SevenFamily208 SevenPrices208 GlobalSeven208
open HarmonicAbel29 ActualRecoveryChain208 RecoveryPrefix208
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem actual_small_false {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 653292 ≤ N) (hhigh : N ≤ 705097) (hF : Legal (Ground N) F) (hcard : B N ≤ F.card)
    (hsmall : (SparseCrooked N 11 F).card ≤ 57841*N) : False := by
  have hd := PaddedCommon212.actual_sparse_density (by omega : 100000 ≤ N) hhigh hF hcard
  have hn : (653292 : ℝ) ≤ N := by exact_mod_cast hN
  have hs : (57841+Loss : ℝ) ≤ (71/800 : ℝ)*N := by
    norm_num [Loss]
    linarith only [hn]
  have hp := mul_le_mul_of_nonneg_right hs (Nat.cast_nonneg (α := ℝ) N)
  have hc : ((SparseCrooked N 11 F).card : ℝ) ≤ 57841*(N : ℝ) := by exact_mod_cast hsmall
  nlinarith only [hd, hp, hc]

theorem actual_common_root {N : ℕ} {F : Finset (Finset ℤ)} {g u eta light : ℝ}
    (hN : 653292 ≤ N) (hhigh : N ≤ 705097) (hF : Legal (Ground N) F) (hcard : B N ≤ F.card)
    (hg : 0 ≤ g) (hfees : TruncatedGlobal209.NearFees N (SparseCrooked N 11 F) g u eta light)
    (hT : g*N ≤ TruncatedAPResponse209.T)
    (hprice : ReciprocalPrice208.Price (TruncatedAPResponse209.Kappa*g) u
      (eta+968+Loss) (-light) N ≤ (71/800 : ℝ)) :
    ∃ c ∈ Ground N, ∀ S ∈ Retained N 11 F, ¬IsAP S → c ∈ S := by
  let G := SparseCrooked N 11 F
  have hGF : G ⊆ F := actual_sparse_subset N 11 F
  have hG := actual_sparse_legal (r := 11) hF
  have hbad : ∀ S ∈ G, ¬IsAP S := fun S hS => (actual_sparse_membership.mp hS).2.1
  have hpay : ∀ A ⊆ G, (∀ S ∈ A, 242 ≤ S.card) →
      ((G.card : ℝ) ≤ A.card+968*(N : ℝ)) → False := by
    intro A hAG hsize hcover
    have hs := actual_unit_source (hAG.trans hGF) hg (hfees A hAG hsize)
    apply PaddedCommon212.actual_low_false (by omega : 100000 ≤ N) hhigh hF hcard hg hT _ hprice
    linarith only [hs, hcover]
  cases IntegerGlobalCases209.actual_cases (N := N) (G := G) (by decide : 0 < 242) with
  | common c hc hall =>
    exact ⟨c, hc, fun S hS hbad => hall S (Finset.mem_filter.mpr ⟨hS, hbad⟩)⟩
  | small T hT hsize hkernel =>
    have hsmall : (SmallKernel112.Small G 241).Nonempty :=
      ⟨T, Finset.mem_filter.mpr ⟨hT, by omega⟩⟩
    have hk : PrivateFinset.Kernel (Ground N) (SmallKernel112.Small G 241) = ∅ := hkernel
    have hp := SharpSmall212.actual_small_empty_kernel241 (by omega : 1 ≤ N) hG hbad hsmall hk
    exact False.elim (actual_small_false hN hhigh hF hcard hp)
  | whole hlow =>
    exact False.elim (hpay G (le_refl G) hlow (le_add_of_nonneg_right (by positivity)))
  | root_low c hc T hT hmin hlow hhighT =>
    obtain ⟨hTG, hTc⟩ := Finset.mem_filter.mp hT
    have hr := actual_degree_from_omitter hG hbad hTG hTc
    have hb : DegreeBudget N T.card ≤ T.card*N := by
      unfold DegreeBudget
      calc
        _ ≤ ∑ _i ∈ Finset.range T.card, N := Finset.sum_le_sum (fun i hi => by omega)
        _ = _ := by simp [mul_comm]
    have hnat := (hr.trans hb).trans (Nat.mul_le_mul_right N hhighT.le)
    have hroot : ((RootPart G c).card : ℝ) ≤ 968*(N : ℝ) := by exact_mod_cast hnat
    have hpart : ((RootPart G c).card : ℝ)+(Avoiders G c).card = G.card :=
      by exact_mod_cast root_avoider_card_partition G c
    have hcover : (G.card : ℝ) ≤ (Avoiders G c).card+968*(N : ℝ) := by linarith only [hroot, hpart]
    exact False.elim (hpay (Avoiders G c) (Finset.filter_subset _ _)
      (fun S hS => hlow.trans (hmin S hS)) hcover)
  | root_high c hc T hT hmin hlow =>
    exact False.elim (PaddedCommon212.actual_high_false (by omega : 638202 ≤ N) hhigh hF hcard hT hmin hlow)

/-- Every source, cleanup, AP, root and direct-small fee is now actual. -/
theorem actual_closed_root {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 653292 ≤ N) (hhi : N ≤ 659912) (hF : Legal (Ground N) F) (hcard : B N ≤ F.card) :
    ∃ c ∈ Ground N, ∀ S ∈ Retained N 11 F, ¬IsAP S → c ∈ S := by
  have hp := PaddedUnit212.actual_price (by omega : 638202 ≤ N) hhi
  exact actual_common_root hN (by omega) hF hcard
    TruncatedUnitPrices209.nonneg.1 (PaddedUnit212.actual_fees hhi hF) hp.1
    (by simpa only [zero_add] using hp.2)

#print axioms actual_small_false
#print axioms actual_common_root
#print axioms actual_closed_root
end
end JSP233.SharpCommon213
