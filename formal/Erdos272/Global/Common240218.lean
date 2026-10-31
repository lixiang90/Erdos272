import Erdos272.Global.Common240216

/-! The minimum240 classification is valid down to its actual small-kernel
cutoff.  Genuine source fees and the price are still explicit in this module.
The new padded fee consumer discharges them separately. -/
namespace JSP233.Common240218
open StarCompletion APGeometry DenseDeletion40 Density41 SparseSmall39
open PrivateFinset IntrinsicTriples208 SevenFamily208 SevenPrices208 GlobalSeven208
open HarmonicAbel29 ActualRecoveryChain208 RecoveryPrefix208 Common240216
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem actual_low_root_false {N : ℕ} {F : Finset (Finset ℤ)}
    {c : ℤ} {T : Finset ℤ} {g u eta light : ℝ}
    (hN : 642498 ≤ N) (hhigh : N ≤ 705097) (hF : Legal (Ground N) F)
    (hcard : B N ≤ F.card) (hg : 0 ≤ g)
    (hfees : Common240216.NearFees N 240 (SparseCrooked N 11 F) g u eta light)
    (hcap : g*N ≤ TruncatedAPResponse209.T)
    (hprice : ReciprocalPrice208.Price (TruncatedAPResponse209.Kappa*g) u
      (eta+968+Loss) (-light) N ≤ (71/800 : ℝ))
    (hT : T ∈ Avoiders (SparseCrooked N 11 F) c)
    (hmin : ∀ S ∈ Avoiders (SparseCrooked N 11 F) c, T.card ≤ S.card)
    (hlow : 240 ≤ T.card) (hsmall : T.card < 968) : False := by
  let G := SparseCrooked N 11 F
  have hGF : G ⊆ F := actual_sparse_subset N 11 F
  have hG := actual_sparse_legal (r := 11) hF
  have hbad : ∀ S ∈ G, ¬IsAP S := fun S hS => (actual_sparse_membership.mp hS).2.1
  obtain ⟨hTG,hTc⟩ := Finset.mem_filter.mp hT
  have hr := actual_degree_from_omitter hG hbad hTG hTc
  have hb : DegreeBudget N T.card ≤ T.card*N := by
    unfold DegreeBudget
    calc
      _ ≤ ∑ _i ∈ Finset.range T.card, N := Finset.sum_le_sum (fun i hi => by omega)
      _ = _ := by simp [mul_comm]
  have hnat := (hr.trans hb).trans (Nat.mul_le_mul_right N hsmall.le)
  have hroot : ((RootPart G c).card : ℝ) ≤ 968*(N : ℝ) := by exact_mod_cast hnat
  have hpart : ((RootPart G c).card : ℝ)+(Avoiders G c).card = G.card :=
    by exact_mod_cast root_avoider_card_partition G c
  have hsource : ((Avoiders G c).card : ℝ) ≤
      6*g*(∑S∈F,((Pool S).card : ℝ))+u*(N : ℝ)^2+eta*N+light := actual_unit_source
    ((Finset.filter_subset (fun S => c∉S) G).trans hGF) hg
    (hfees (Avoiders G c) (Finset.filter_subset _ _)
      (fun S hS => hlow.trans (hmin S hS)))
  have hcover : (G.card : ℝ) ≤ (Avoiders G c).card+968*(N : ℝ) := by
    linarith only [hroot,hpart]
  apply PaddedCommon212.actual_low_false (by omega : 100000 ≤ N) hhigh hF hcard
    hg hcap _ hprice
  have hpaid : (G.card : ℝ) ≤
      6*g*(∑S∈F,((Pool S).card : ℝ))+u*(N : ℝ)^2+eta*N+light+968*N := by
    linarith only [hcover,hsource]
  exact hpaid

theorem actual_common_root {N : ℕ} {F : Finset (Finset ℤ)} {g u eta light : ℝ}
    (hN : 642498 ≤ N) (hhigh : N ≤ 705097) (hF : Legal (Ground N) F)
    (hcard : B N ≤ F.card) (hg : 0 ≤ g)
    (hfees : Common240216.NearFees N 240 (SparseCrooked N 11 F) g u eta light)
    (hcap : g*N ≤ TruncatedAPResponse209.T)
    (hprice : ReciprocalPrice208.Price (TruncatedAPResponse209.Kappa*g) u
      (eta+968+Loss) (-light) N ≤ (71/800 : ℝ)) :
    ∃ c ∈ Ground N, ∀ S ∈ Retained N 11 F, ¬IsAP S → c∈S := by
  let G := SparseCrooked N 11 F
  have hGF : G ⊆ F := actual_sparse_subset N 11 F
  have hG := actual_sparse_legal (r := 11) hF
  have hbad : ∀ S ∈ G, ¬IsAP S := fun S hS => (actual_sparse_membership.mp hS).2.1
  cases IntegerGlobalCases209.actual_cases (N := N) (G := G) (by decide : 0 < 240) with
  | common c hc hall =>
    exact ⟨c,hc,fun S hS hbad => hall S (Finset.mem_filter.mpr ⟨hS,hbad⟩)⟩
  | small T hT hsize hkernel =>
    have hsmall : (SmallKernel112.Small G 239).Nonempty :=
      ⟨T,Finset.mem_filter.mpr ⟨hT,by omega⟩⟩
    have hk : Kernel (Ground N) (SmallKernel112.Small G 239) = ∅ := hkernel
    have hp := SharpSmall212.actual_small_empty_kernel_whole (by omega : 1 ≤ N)
      (by decide : 2 ≤ 239) hG hbad hsmall hk
    have hp' : G.card ≤ 56883*N := by simpa using hp
    exact False.elim (Common240216.actual_small_false hN hhigh hF hcard hp')
  | whole hlow =>
    have hs := actual_unit_source hGF hg (hfees G (le_refl G) hlow)
    apply False.elim
    apply PaddedCommon212.actual_low_false (by omega : 100000 ≤ N) hhigh hF hcard
      hg hcap _ hprice
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    linarith only [hs,hN0]
  | root_low c hc T hT hmin hlow hhighT =>
    exact False.elim (actual_low_root_false hN hhigh hF hcard hg hfees hcap hprice
      hT hmin hlow (by omega))
  | root_high c hc T hT hmin hlow =>
    by_cases hsmall : T.card < 968
    · exact False.elim (actual_low_root_false hN hhigh hF hcard hg hfees hcap hprice
        hT hmin (by omega) hsmall)
    · exact False.elim (PaddedCommon212.actual_high_false (by omega : 638202 ≤ N)
        hhigh hF hcard hT hmin (by omega))

#print axioms actual_low_root_false
#print axioms actual_common_root
end
end JSP233.Common240218
