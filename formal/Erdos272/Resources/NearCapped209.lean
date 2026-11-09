module

public import Erdos272.Resources.NearResidual208
public import Erdos272.Resources.CappedResidual209
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

namespace JSP233.NearCapped209
open StarCompletion APGeometry NearAP36 ResidualStratum208 ResidualGlobal208
open PartitionCleanup208 ResidualAggregate208 ResidualTwoCensus208
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0

def Price (M e c : ℕ) : ℝ :=
  (∑b∈Finset.Icc 2 c,(1/((M-b : ℕ) : ℝ)+1/((2*M-3*b : ℕ) : ℝ))/((b : ℝ)*(b-1)))+
    (2/((M-e : ℕ) : ℝ))/(c : ℝ)

theorem actual_near_payment {ι : Type*} [DecidableEq ι]
    {N D M e c : ℕ} {F : Finset (Finset ℤ)} (hF : Legal (Ground N) F)
    (he : 2 ≤ e) (heM : e < M) (hc : 1≤c) (hce : c<e) (hshort : 3*c<2*M)
    (core : Finset ℤ → Finset ℤ) (step : Finset ℤ → ℕ)
    (hstep : ∀ S ∈ F, step S ∈ Finset.Icc 1 D)
    (hsub : ∀ S ∈ F, core S ⊆ S)
    (hAt : ∀ S ∈ F, ∃ a : ℤ, APAt (step S : ℤ) a (core S))
    (hne : ∀ S ∈ F, (core S).Nonempty)
    (hmax : ∀ S ∈ F, ∀ R : Finset ℤ, IsAP R → R ⊆ S → R.card ≤ (core S).card)
    (hsize : ∀ S ∈ F, M ≤ S.card) (hbad : ∀ S ∈ F, ¬IsAP S)
    (hsmall : ∀ S ∈ F, (S \ core S).card < e)
    (U : ℕ → Finset ℤ) (hU : ∀ S ∈ F, core S ⊆ U (step S))
    (label : Finset ℤ → ι) (I : ℕ → Finset ι)
    (hlabel : ∀ S ∈ F, label S ∈ I (step S))
    (hdis : ∀ S ∈ F, ∀ T ∈ F, S ≠ T → step S=step T → label S=label T →
      Disjoint (S \ core S) (T \ core T)) :
    (F.card : ℝ) ≤ (N : ℝ)^2*Price M e c+
      ((∑ d ∈ Finset.Icc 1 D, (I d).card*((U d).card+(e-1)) : ℕ) : ℝ) := by
  have hcore : ∀ S ∈ F, MaximalAPCore S (core S) := by
    intro S hS
    obtain ⟨a,hA⟩ := hAt S hS
    obtain ⟨t,ht⟩ := hne S hS
    exact maximum_is_maximal (hsub S hS)
      ((isAP_iff_exists_APAt _).mpr ⟨step S,t,apAt_rebase hA ht,ht⟩) (hmax S hS)
  obtain ⟨G,point,hGF,ht,hpay⟩ := actual_step_cleanup hF core step hstep hcore hAt hne
    U hU label I hlabel hdis hsmall
  have hG : Legal (Ground N) G := ⟨fun S hS => hF.1 S (hGF hS),
    fun S hS T hT hST => hF.2 S (hGF hS) T (hGF hT) hST⟩
  have hGAt : ∀ S ∈ G, APAt (step S : ℤ) (point (step S)) (core S) := by
    intro S hS
    obtain ⟨a,hA⟩ := hAt S (hGF hS)
    exact apAt_rebase hA (ht S hS)
  have hp := CappedResidual209.actual_global_residual hG hc hce heM hshort core step point (fun S hS => hstep S (hGF hS))
    (fun S hS => hsub S (hGF hS)) hGAt ht (fun S hS => hsize S (hGF hS))
    (fun S hS => hbad S (hGF hS)) (fun S hS => hsmall S (hGF hS)) (fun S hS => hmax S (hGF hS))
  have hR : (F.card : ℝ) ≤ (G.card : ℝ)+
      ((∑ d ∈ Finset.Icc 1 D, (I d).card*((U d).card+(e-1)) : ℕ) : ℝ) := by exact_mod_cast hpay
  have hpc : (G.card : ℝ)≤(N : ℝ)^2*Price M e c := by
    simpa only [Price] using hp
  linarith only [hR,hpc]

#print axioms actual_near_payment
end
end JSP233.NearCapped209
