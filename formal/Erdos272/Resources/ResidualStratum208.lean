import Erdos272.Resources.ResidualOccupancy208
import Erdos272.Arithmetic.StepClass208

namespace JSP233.ResidualStratum208
open StarCompletion APGeometry NearAP36 ResidualOccupancy208 ResidualSpan208
open StepClass208
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0

theorem maximum_is_maximal {S P : Finset ℤ} (hsub : P ⊆ S) (hAP : IsAP P)
    (hmax : ∀ R : Finset ℤ, IsAP R → R ⊆ S → R.card ≤ P.card) : MaximalAPCore S P := by
  refine ⟨hsub,hAP,?_⟩
  intro R hPR hRS hR
  exact (Finset.eq_of_subset_of_card_le hPR (hmax R hR hRS)).symm

theorem actual_defect_stratum {N M b d : ℕ} {F : Finset (Finset ℤ)} {t : ℤ}
    (hF : Legal (Ground N) F) (hb : b ≤ M)
    (core : Finset ℤ → Finset ℤ)
    (hsub : ∀ S ∈ F, core S ⊆ S)
    (hAt : ∀ S ∈ F, APAt (d : ℤ) t (core S)) (ht : ∀ S ∈ F, t ∈ core S)
    (hsize : ∀ S ∈ F, M ≤ S.card)
    (hmax : ∀ S ∈ F, ∀ R : Finset ℤ, IsAP R → R ⊆ S → R.card ≤ (core S).card)
    (x : ℤ) :
    (F.filter (fun S => x ∈ S \ core S ∧ (S \ core S).card < b)).card ≤
      (if (d : ℤ)*(M-b : ℕ) ≤ (N : ℤ)-1 then 1 else 0)+
      (if (d : ℤ)*(Span (M-b) b (PrimeGate d) : ℤ) ≤ (N : ℤ)-1 then 1 else 0) := by
  let H := F.filter (fun S => (S \ core S).card < b)
  have hHF : H ⊆ F := Finset.filter_subset _ _
  have hH : Legal (Ground N) H := ⟨fun S hS => hF.1 S (hHF hS),
    fun S hS T hT hST => hF.2 S (hHF hS) T (hHF hT) hST⟩
  have hp : 2 ≤ PrimeGate d := by
    have hr := primeGate_range d
    simp only [Finset.mem_insert,Finset.mem_singleton] at hr
    omega
  have hcore : ∀ S ∈ H, MaximalAPCore S (core S) := by
    intro S hS
    exact maximum_is_maximal (hsub S (hHF hS))
      ((isAP_iff_exists_APAt _).mpr ⟨d,t,hAt S (hHF hS),ht S (hHF hS)⟩) (hmax S (hHF hS))
  have hcard : ∀ S ∈ H, M-b+1 ≤ (core S).card := by
    intro S hS
    have hs := hsize S (hHF hS)
    have hsmall := (Finset.mem_filter.mp hS).2
    have hc := Finset.card_sdiff_add_card_eq_card (hsub S (hHF hS))
    omega
  have hc := actual_cumulative_occupancy (b := b) hH hp core hcore (fun S hS => hAt S (hHF hS))
    (fun S hS => ht S (hHF hS)) hcard (fun S hS => hmax S (hHF hS))
    (fun delta hdelta hdiv hlt => actual_ratio d hdelta hdiv hlt) x
  have heq : H.filter (fun S => x ∈ S \ core S ∧ (S \ core S).card < b)=
      F.filter (fun S => x ∈ S \ core S ∧ (S \ core S).card < b) := by
    ext S
    simp only [H,Finset.mem_filter]
    tauto
  rw [heq] at hc
  exact hc

#print axioms maximum_is_maximal
#print axioms actual_defect_stratum
end
end JSP233.ResidualStratum208
