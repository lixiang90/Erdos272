import Erdos272.Resources.IntegerHeavyBridge209

namespace JSP233.IntegerUniformFees209
open StarCompletion APGeometry SevenFamily208
open CrossBandCredit208 CrossBandCredit208.System CrossBandCleanup208
open IntegerUniformProfiles209 IntegerUniformRows209 IntegerHighPrices209
open IntegerUniformLight209 IntegerUniformHeavyData209
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 200000
local notation "Grid" => ResidualCeil208.Grid

def bill (N : ℕ) (w : Fin 11) (k : ℕ) : ℝ :=
  (alphaUnits w k : ℝ)/(Grid : ℝ)*(N : ℝ)^2+
    ((etaLight w k+heavyCeiling w k : ℕ) : ℝ)*N

theorem actual_layer {N : ℕ} {A : Finset (Finset ℤ)}
    (w : Fin 11) (i : Fin (count w)) (hN : 2≤N) (hhi : N≤Upper w)
    (hlegal : Legal (Ground N) A) (hbad : ∀S∈A,¬IsAP S)
    (hsize : ∀S∈A,M w≤S.card) (hsparse : ∀S∈A,11*S.card≤N) :
    ((JointNear N A 1 (M w) (psi w) i.val).card : ℝ)≤bill N w i.val := by
  obtain ⟨s,hsN,hsD,hsM,hse,hsF,hfields,v⟩:=actual_system w i hN hhi hlegal hbad hsize hsparse
  have hd : s.D≤s.N := by rw [hsD,hsN];exact Nat.div_le_self _ _
  have hn : 0<s.N := by omega
  have hhv:=IntegerHeavyBridge209.actual_heavy w i s v hn hse (fun d hd b=>hfields d b)
  have hl:=actual_residual_light w i s v (by omega) hd (fun d hd b=>hfields d b)
  obtain ⟨hc,hce,hshort⟩:=cut_valid w i
  have hp:=FullBandCleanup209.actual_full_near_bound s v (c := cut w i.val)
    hc (by rwa [hse]) (by rwa [hsM])
  have hlight : FullBandCleanup209.LightTotal s=
      ∑d∈Finset.Icc 1 s.D,∑b : Fin 7,ActualLightAnalytic209.EffectiveLight s d b := rfl
  rw [hlight,hsM,hse] at hp
  rw [hsF] at hp
  rw [hsN] at hp hhv hl
  unfold bill
  push_cast
  linarith only [hp,hhv,hl]

theorem weighted_bill (N : ℕ) (w : Fin 11) :
    (∑i∈Finset.range (count w),(psi w (i+1)-psi w i)*bill N w i)/psi w (count w)≤
      IntegerRobustPrices209.U w*(N : ℝ)^2+(IntegerRobustPrices209.Eta w : ℝ)*N := by
  have hm:=mul_le_mul_of_nonneg_right (main_budget w) (sq_nonneg (N : ℝ))
  have he:=mul_le_mul_of_nonneg_right (eta_budget w) (Nat.cast_nonneg (α := ℝ) N)
  have hmain : (∑i∈Finset.range (count w),(psi w (i+1)-psi w i)*
      ((alphaUnits w i : ℝ)/(Grid : ℝ)*(N : ℝ)^2))=
      (∑i∈Finset.range (count w),(psi w (i+1)-psi w i)*(alphaUnits w i : ℝ)/(Grid : ℝ))*(N : ℝ)^2 := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hlinear : (∑i∈Finset.range (count w),(psi w (i+1)-psi w i)*
      (((etaLight w i+heavyCeiling w i : ℕ) : ℝ)*N))=
      (∑i∈Finset.range (count w),(psi w (i+1)-psi w i)*
        ((etaLight w i+heavyCeiling w i : ℕ) : ℝ))*(N : ℝ) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hexpand : (∑i∈Finset.range (count w),(psi w (i+1)-psi w i)*bill N w i)/psi w (count w)=
      ((∑i∈Finset.range (count w),(psi w (i+1)-psi w i)*(alphaUnits w i : ℝ)/(Grid : ℝ))/psi w (count w))*(N : ℝ)^2+
      ((∑i∈Finset.range (count w),(psi w (i+1)-psi w i)*
        ((etaLight w i+heavyCeiling w i : ℕ) : ℝ))/psi w (count w))*(N : ℝ) := by
    unfold bill
    simp only [mul_add,Finset.sum_add_distrib]
    rw [hmain,hlinear]
    ring
  rw [hexpand]
  exact add_le_add hm he

/-- The explicit real family deficiency obligation, with all actual light,
full-heavy, right-middle and capped remainder charges paid. -/
theorem actual_obligation {N : ℕ} {A : Finset (Finset ℤ)}
    (w : Fin 11) (hN : 2≤N) (hhi : N≤Upper w)
    (hlegal : Legal (Ground N) A) (hbad : ∀S∈A,¬IsAP S)
    (hsize : ∀S∈A,M w≤S.card) (hsparse : ∀S∈A,11*S.card≤N) :
    IntegerShared209.NearObligation N A (M w)
      (IntegerRobustPrices209.G w) (IntegerRobustPrices209.U w) (IntegerRobustPrices209.Eta w) := by
  refine ⟨psi w,count w,psi_mono w,psi_zero w,psi_pos w,reciprocal w,?_⟩
  have hh : (∑i∈Finset.range (count w),(psi w (i+1)-psi w i)*
      ((JointNear N A 1 (M w) (psi w) i).card : ℝ))≤
      ∑i∈Finset.range (count w),(psi w (i+1)-psi w i)*bill N w i := by
    apply Finset.sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonneg_left
      (actual_layer w ⟨i,Finset.mem_range.mp hi⟩ hN hhi hlegal hbad hsize hsparse)
      (sub_nonneg.mpr (psi_mono w (Nat.le_succ i)))
  exact (div_le_div_of_nonneg_right hh (psi_pos w).le).trans (weighted_bill N w)

#print axioms actual_layer
#print axioms weighted_bill
#print axioms actual_obligation
end
end JSP233.IntegerUniformFees209
