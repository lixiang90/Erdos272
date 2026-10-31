import Erdos272.Counting.ActualNearBlock208
import Erdos272.Resources.RightWindows208

namespace JSP233.BandGeometry208
open StarCompletion APGeometry NearAP36 SourceBridge208 CoreCoordinates208
open StepClass208 ShiftedBlocks208 PotentialPhases208
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0

theorem actual_traits {N d T E U : ℕ} {F : Finset (Finset ℤ)}
    (hF : Legal (Ground N) F) (hd : 0 < d) (hT : 2 ≤ T) (hET : E ≤ T)
    (start : Finset ℤ → ℕ)
    (hbad : ∀ S ∈ F, ¬IsAP S) (hlow : ∀ S ∈ F, T ≤ S.card)
    (hhigh : ∀ S ∈ F, S.card < U) (hsmall : ∀ S ∈ F, Defect S < E)
    (hsub : ∀ S ∈ F, Grid (start S) d (MaxAPSize S) ⊆ S) :
    ∀ S ∈ F, T-E+1 ≤ MaxAPSize S ∧ MaxAPSize S ≤ U-2 ∧
      (S \ Grid (start S) d (MaxAPSize S)).card=Defect S ∧ 1 ≤ start S := by
  intro S hS
  have hs := hlow S hS
  have hhi := hhigh S hS
  have he := hsmall S hS
  have hm := maxAPSize_le_card S
  have hp := defect_positive (by omega : 2 ≤ S.card) (hF.1 S hS) (hbad S hS)
  have hc := Finset.card_sdiff_add_card_eq_card (hsub S hS)
  rw [grid_card _ _ _ hd] at hc
  have hmlow : T-E+1 ≤ MaxAPSize S := by unfold Defect at he; omega
  have hmax : MaxAPSize S ≤ U-2 := by unfold Defect at hp; omega
  have hrem : (S \ Grid (start S) d (MaxAPSize S)).card=Defect S := by unfold Defect; omega
  have haS : (start S : ℤ) ∈ S :=
    hsub S hS ((mem_grid _ _ _ _).mpr ⟨0,by omega,by simp⟩)
  have ha : 1 ≤ start S := by exact_mod_cast ((mem_ground N _).mp (hF.1 S hS haS)).1
  exact ⟨hmlow,hmax,hrem,ha⟩

theorem actual_band_windows {N d T E U B : ℕ} {F : Finset (Finset ℤ)}
    (hF : Legal (Ground N) F) (hd : 0 < d) (hT : 2 ≤ T) (hET : E ≤ T)
    (hB : 2 ≤ B) (start : Finset ℤ → ℕ)
    (hbad : ∀ S ∈ F, ¬IsAP S) (hlow : ∀ S ∈ F, T ≤ S.card)
    (hhigh : ∀ S ∈ F, S.card < U) (hsmall : ∀ S ∈ F, Defect S < E)
    (hsub : ∀ S ∈ F, Grid (start S) d (MaxAPSize S) ⊆ S) :
    ∀ S ∈ F,
      Grid (start S) d (MaxAPSize S) ⊆
        ClippedWindows208.Window N d B (U+B-3) (Code d B (start S)) ∧
      S.card ≤ min (U+B-3) (N/d-(Code d B (start S)).2*B+E) ∧
      (Code d B (start S)).1 < d ∧
      T-E+(Code d B (start S)).2*B ≤ N/d := by
  intro S hS
  obtain ⟨hm,hmax,hrem,ha⟩ := actual_traits hF hd hT hET start hbad hlow hhigh hsmall hsub S hS
  have hU : 3 ≤ U := by have := hlow S hS; have := hhigh S hS; omega
  have hE : 1 ≤ E := by have := hsmall S hS; omega
  have hwin := ShiftedWindows208.core_in_window (d := d) ha (by omega : 0 < B)
    (by omega : MaxAPSize S+B-1 ≤ U+B-3)
  have hcore : Grid (start S) d (MaxAPSize S) ⊆
      ClippedWindows208.Window N d B (U+B-3) (Code d B (start S)) := by
    intro x hx
    exact Finset.mem_inter.mpr ⟨hwin hx,hF.1 S hS (hsub S hS hx)⟩
  have hsize : S.card=MaxAPSize S+Defect S := by have := maxAPSize_le_card S; unfold Defect; omega
  have hcap := actual_source_cap hd (by omega : 0 < B) (by omega : 0 < MaxAPSize S)
    (hsmall S hS) hsize (hsub S hS) (hF.1 S hS)
  have hphase := actual_code_phase hd (by omega : 0 < B) hm (hsub S hS) (hF.1 S hS)
  have hp := (Finset.mem_filter.mp hphase).2
  have hprod : (T-E+(Code d B (start S)).2*B)*d ≤ N := by omega
  refine ⟨hcore,le_min (by have := hhigh S hS; omega) hcap,?_,?_⟩
  · exact Nat.mod_lt _ hd
  · exact (Nat.le_div_iff_mul_le hd).mpr hprod

theorem actual_band_disjoint {N d T E U B : ℕ} {F : Finset (Finset ℤ)}
    (hF : Legal (Ground N) F) (hd : 0 < d) (hT : 2 ≤ T) (hET : E ≤ T)
    (hB : 0 < B) (hBA : B ≤ T-E) (start : Finset ℤ → ℕ)
    (hbad : ∀ S ∈ F, ¬IsAP S) (hlow : ∀ S ∈ F, T ≤ S.card)
    (hhigh : ∀ S ∈ F, S.card < U) (hsmall : ∀ S ∈ F, Defect S < E)
    (hsub : ∀ S ∈ F, Grid (start S) d (MaxAPSize S) ⊆ S)
    (hgate : (PrimeGate d-1)*(T-E+1-B) ≥ E ∨
      PrimeGate d*B ≤ (PrimeGate d-1)*(T-E+1)) :
    ∀ S ∈ F, ∀ R ∈ F, S ≠ R → Code d B (start S)=Code d B (start R) →
      Disjoint (S \ Grid (start S) d (MaxAPSize S))
        (R \ Grid (start R) d (MaxAPSize R)) := by
  intro S hS R hR hne hcode
  obtain ⟨hmS,hmaxS,hremS,haS⟩ := actual_traits hF hd hT hET start hbad hlow hhigh hsmall hsub S hS
  obtain ⟨hmR,hmaxR,hremR,haR⟩ := actual_traits hF hd hT hET start hbad hlow hhigh hsmall hsub R hR
  have hp : 2 ≤ PrimeGate d := by unfold PrimeGate; split_ifs <;> norm_num
  exact actual_pair_remainders_disjoint hF hS hR hne hd hB hBA hp hmS hmR hcode
    (hsub S hS) (hsub R hR) (by rw [hremS]; exact hsmall S hS)
    (by rw [hremR]; exact hsmall R hR) hgate
    (fun delta hdelta hdiv hlt => actual_ratio d hdelta hdiv hlt)
    (fun P hP hPS => AP_card_le_max hP hPS)
    (fun P hP hPR => AP_card_le_max hP hPR)

#print axioms actual_traits
#print axioms actual_band_windows
#print axioms actual_band_disjoint
end
end JSP233.BandGeometry208
