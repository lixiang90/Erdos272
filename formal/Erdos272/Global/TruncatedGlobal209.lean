module

public import Erdos272.Resources.TruncatedAPResponse209
public import Erdos272.Global.LowHighRoot209
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

namespace JSP233.TruncatedGlobal209
open StarCompletion APGeometry DenseDeletion40 Density41 SparseSmall39
open PrivateFinset IntrinsicTriples208 SevenFamily208 SevenPrices208 GlobalSeven208
open HarmonicAbel29 ActualRecoveryChain208 RecoveryPrefix208
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem actual_low_false {N : ℕ} {F : Finset (Finset ℤ)} {g u eta light : ℝ}
    (hN : 659912≤N) (hhigh : N≤705097) (hF : Legal (Ground N) F) (hcard : B N≤F.card)
    (hg : 0≤g) (hT : g*N≤TruncatedAPResponse209.T)
    (hsource : ((SparseCrooked N 11 F).card : ℝ)≤
      6*g*(∑S∈F,((Pool S).card : ℝ))+u*(N : ℝ)^2+eta*N+light+968*N)
    (hprice : ReciprocalPrice208.Price (TruncatedAPResponse209.Kappa*g) u
      (eta+968+Loss) (-light) N≤(71/800 : ℝ)) : False := by
  have hfull : ((F.filter fun S=>¬IsAP S).card : ℝ)≤
      6*g*(∑S∈F,((Pool S).card : ℝ))+
        (u*(N : ℝ)^2+eta*N+light+968*N+(Deleted N 11 F).card) := by
    rw [crooked_partition N F]
    linarith only [hsource]
  have hj:=TruncatedAPResponse209.actual_joint_any_AP (by omega : 2≤N) hF hg hT hfull
  have hlow:=original_lower hcard
  have hd:=DenseDeletion208.actual_deleted11_affine (by omega : 10902≤N) hF
  have hdR : ((Deleted N 11 F).card : ℝ)≤121*(N : ℝ)+968 := by exact_mod_cast hd
  have hn : (659912 : ℝ)≤N := by exact_mod_cast hN
  have hn0 : (N : ℝ)≠0 := by exact_mod_cast (show N≠0 by omega)
  have hpaid:=mul_le_mul_of_nonneg_right hprice (sq_nonneg (N : ℝ))
  have he : ReciprocalPrice208.Price (TruncatedAPResponse209.Kappa*g) u
      (eta+968+Loss) (-light) N*(N : ℝ)^2=
      TruncatedAPResponse209.Kappa*g*(N : ℝ)^3+u*(N : ℝ)^2+(eta+968+Loss)*N+light := by
    unfold ReciprocalPrice208.Price
    field_simp
    <;> ring
  rw [he] at hpaid
  have hh:=mul_le_mul_of_nonneg_right (harmonic_cap (by omega : 100000≤N) hhigh)
    (Nat.cast_nonneg (α := ℝ) N)
  have hmargin : (HCap+122-Loss)*(N : ℝ)+968<0 := by
    norm_num [HCap,Loss]
    linarith only [hn]
  nlinarith only [hj,hlow,hdR,hpaid,hh,hmargin]

def NearFees (N : ℕ) (G : Finset (Finset ℤ)) (g u eta light : ℝ) : Prop :=
  ∀A⊆G,(∀S∈A,242≤S.card)→UnitNearObligation N A g u eta light

/-- One actual small subfamily and minimum omitter give the complete
classification. Both low-root cases use the same unit242 source and 968N. -/
theorem actual_common_root {N : ℕ} {F : Finset (Finset ℤ)} {g u eta light : ℝ}
    (hN : 659912≤N) (hhigh : N≤705097) (hF : Legal (Ground N) F) (hcard : B N≤F.card)
    (hg : 0≤g) (hfees : NearFees N (SparseCrooked N 11 F) g u eta light)
    (hT : g*N≤TruncatedAPResponse209.T)
    (hprice : ReciprocalPrice208.Price (TruncatedAPResponse209.Kappa*g) u
      (eta+968+Loss) (-light) N≤(71/800 : ℝ)) :
    ∃c∈Ground N,∀S∈Retained N 11 F,¬IsAP S→c∈S := by
  let G:=SparseCrooked N 11 F
  have hGF : G⊆F:=actual_sparse_subset N 11 F
  have hG:=actual_sparse_legal (r := 11) hF
  have hbad : ∀S∈G,¬IsAP S:=fun S hS=>(actual_sparse_membership.mp hS).2.1
  have htwo:=actual_sparse_two hN hhigh hF hcard
  have hpay : ∀A⊆G,(∀S∈A,242≤S.card)→
      ((G.card : ℝ)≤A.card+968*(N : ℝ))→False := by
    intro A hAG hsize hcover
    have hs:=actual_unit_source (hAG.trans hGF) hg (hfees A hAG hsize)
    apply actual_low_false hN hhigh hF hcard hg hT _ hprice
    linarith only [hs,hcover]
  cases IntegerGlobalCases209.actual_cases (N := N) (G := G) (by decide : 0<242) with
  | common c hc hall =>
    exact ⟨c,hc,fun S hS hbad=>hall S (Finset.mem_filter.mpr ⟨hS,hbad⟩)⟩
  | small T hT hsize hkernel =>
    have hp:=IntegerWindowEndpoints209.actual_coarse_small_payment hG hbad htwo hT hsize hkernel
    have hp' : G.card≤58081*N:=by norm_num at hp;exact hp
    exact False.elim (actual_small_branch_false hN hhigh hF hcard hp')
  | whole hlow =>
    exact False.elim (hpay G (le_refl G) hlow (le_add_of_nonneg_right (by positivity)))
  | root_low c hc T hT hmin hlow hhighT =>
    obtain ⟨hTG,hTc⟩:=Finset.mem_filter.mp hT
    have hr:=actual_degree_from_omitter hG hbad hTG hTc
    have hb : DegreeBudget N T.card≤T.card*N := by
      unfold DegreeBudget
      calc
        _≤∑_i∈Finset.range T.card,N := Finset.sum_le_sum (fun i hi=>by omega)
        _=_ := by simp [mul_comm]
    have hnat:=(hr.trans hb).trans (Nat.mul_le_mul_right N hhighT.le)
    have hroot : ((RootPart G c).card : ℝ)≤968*(N : ℝ) := by exact_mod_cast hnat
    have hpart : ((RootPart G c).card : ℝ)+(Avoiders G c).card=G.card :=
      by exact_mod_cast root_avoider_card_partition G c
    have hcover : (G.card : ℝ)≤(Avoiders G c).card+968*(N : ℝ) := by linarith only [hroot,hpart]
    exact False.elim (hpay (Avoiders G c) (Finset.filter_subset _ _)
      (fun S hS=>hlow.trans (hmin S hS)) hcover)
  | root_high c hc T hT hmin hlow =>
    exact False.elim (LowHighRoot209.actual_high_false hN hhigh hF hcard hT hmin hlow)

theorem actual_original_upper {N : ℕ} {F : Finset (Finset ℤ)} {g u eta light : ℝ}
    (hN : 659912≤N) (hhigh : N≤705097) (hF : Legal (Ground N) F)
    (hg : 0≤g) (hfees : NearFees N (SparseCrooked N 11 F) g u eta light)
    (hT : g*N≤TruncatedAPResponse209.T)
    (hprice : ReciprocalPrice208.Price (TruncatedAPResponse209.Kappa*g) u
      (eta+968+Loss) (-light) N≤(71/800 : ℝ)) : F.card≤B N := by
  by_cases hc : B N≤F.card
  · exact RootedWindow209.actual_original_upper_of_root11 hN hhigh hF
      (actual_common_root hN hhigh hF hc hg hfees hT hprice)
  · omega

#print axioms actual_low_false
#print axioms actual_common_root
#print axioms actual_original_upper
end
end JSP233.TruncatedGlobal209
