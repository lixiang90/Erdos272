module

public import Erdos272.Resources.ResidualStratum208
public import Erdos272.Resources.ResidualWeights208
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

namespace JSP233.ResidualPrice208
open StarCompletion APGeometry NearAP36 ResidualSpan208 ResidualStratum208
open ResidualWeights208 CoreCleanup208 StepClass208
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0

def Occupancy (N M d b : ℕ) : ℕ :=
  (if (d : ℤ)*(M-b : ℕ) ≤ (N : ℤ)-1 then 1 else 0)+
  (if (d : ℤ)*(Span (M-b) b (PrimeGate d) : ℤ) ≤ (N : ℤ)-1 then 1 else 0)

def DiscretePrice (N M d e : ℕ) : ℝ :=
  (Occupancy N M d e : ℝ)/((e-1 : ℕ) : ℝ)+
    ∑ b ∈ Finset.Ico 2 e, (Occupancy N M d b : ℝ)/((b : ℝ)*(b-1))

theorem actual_step_price {N M d e : ℕ} {F : Finset (Finset ℤ)} {t : ℤ}
    (hF : Legal (Ground N) F) (he : 2 ≤ e) (heM : e ≤ M)
    (core : Finset ℤ → Finset ℤ)
    (hsub : ∀ S ∈ F, core S ⊆ S)
    (hAt : ∀ S ∈ F, APAt (d : ℤ) t (core S)) (ht : ∀ S ∈ F, t ∈ core S)
    (hsize : ∀ S ∈ F, M ≤ S.card) (hbad : ∀ S ∈ F, ¬IsAP S)
    (hsmall : ∀ S ∈ F, (S \ core S).card < e)
    (hmax : ∀ S ∈ F, ∀ R : Finset ℤ, IsAP R → R ⊆ S → R.card ≤ (core S).card) :
    (F.card : ℝ) ≤ (N : ℝ)*DiscretePrice N M d e := by
  let piece := fun S => S \ core S
  have hpos : ∀ S ∈ F, 0 < (piece S).card := by
    intro S hS
    by_contra hn
    have hzero : (S \ core S).card=0 := by dsimp [piece] at hn; omega
    have hh := Finset.card_sdiff_add_card_eq_card (hsub S hS)
    have heq : core S=S := Finset.eq_of_subset_of_card_le (hsub S hS) (by omega)
    apply hbad S hS
    rw [←heq]
    exact (isAP_iff_exists_APAt _).mpr ⟨d,t,hAt S hS,ht S hS⟩
  have hcap : ∀ x ∈ Ground N, ∀ b, 2 ≤ b → b ≤ e →
      (Cumulative F piece x b : ℝ) ≤ (Occupancy N M d b : ℝ) := by
    intro x hx b hb2 hbe
    have hc := actual_defect_stratum hF (hbe.trans heM) core hsub hAt ht hsize hmax x
    exact_mod_cast hc
  have hp := cumulative_source_bound F (Ground N) piece e (fun b => (Occupancy N M d b : ℝ)) he
    (fun S hS => Finset.sdiff_subset.trans (hF.1 S hS)) hpos hsmall hcap
  simpa only [ground_card,DiscretePrice] using hp

#print axioms actual_step_price
end
end JSP233.ResidualPrice208
