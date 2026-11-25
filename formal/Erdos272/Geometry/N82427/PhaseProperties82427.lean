module

public import Erdos272.Geometry.N82427.PhaseGeometry82427

@[expose] public section

namespace JSP233.PhaseProperties82427
open StarCompletion APGeometry NearAP36 SourceBridge208 ShiftedBlocks208 ClippedWindows208
open PhaseDefs82427 PhaseGeometry82427 BandLabels208
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

theorem actual_properties {N d T E U B : ℕ} {F : Finset (Finset ℤ)}
    (hF : Legal (Ground N) F) (hd : 0 < d) (hT : 2 ≤ T) (hET : E ≤ T)
    (hE : 2 ≤ E) (hTU : T < U) (hB : 3 ≤ B) (hBA : B ≤ T-E)
    (start : Finset ℤ → ℕ)
    (hbad : ∀ S ∈ F, ¬IsAP S) (hlow : ∀ S ∈ F, T ≤ S.card)
    (hhigh : ∀ S ∈ F, S.card < U) (hsmall : ∀ S ∈ F, Defect S < E)
    (hsub : ∀ S ∈ F, Grid (start S) d (MaxAPSize S) ⊆ S)
    (hgate : (StepClass208.PrimeGate d-1)*(T-E+1-B) ≥ E ∨
      StepClass208.PrimeGate d*B ≤ (StepClass208.PrimeGate d-1)*(T-E+1)) :
    BandSystem208.Properties N d (T-E) B (U+B-3) E
      (PhaseDefs82427.Heavy N d B U E F start) := by
  let V := U+B-3
  let H := PhaseDefs82427.Heavy N d B U E F start
  let family := BandSystem208.Fiber F d B start
  let core : Finset ℤ → Finset ℤ := fun S => Grid (start S) d (MaxAPSize S)
  let theta : (ℕ × ℕ) → ℕ := fun q => Cap N d E B V (Swap q)
  have hEV : E ≤ V := by dsimp only [V]; omega
  have hUV : U-1 ≤ V-1 := by dsimp only [V]; omega
  have hw := BandGeometry208.actual_band_windows hF hd hT hET (by omega : 2 ≤ B)
    start hbad hlow hhigh hsmall hsub
  have hrem := BandGeometry208.actual_band_disjoint hF hd hT hET (by omega : 0 < B)
    hBA start hbad hlow hhigh hsmall hsub hgate
  have hmem : ∀ q, ∀ S ∈ family q, S ∈ F ∧ Code d B (start S)=q := by
    intro q S hS
    exact Finset.mem_filter.mp hS
  have himage : ∀ q ∈ H, ∃ S ∈ F, Code d B (start S)=q := by
    intro q hq
    exact Finset.mem_image.mp (Finset.mem_filter.mp hq).1
  have hres : ∀ q ∈ H, q.1 < d := by
    intro q hq
    obtain ⟨S, hS, heq⟩ := himage q hq
    simpa only [heq] using (hw S hS).2.2.1
  have hfeasible : ∀ q ∈ H, T-E+q.2*B ≤ N/d := by
    intro q hq
    obtain ⟨S, hS, heq⟩ := himage q hq
    simpa only [heq] using (hw S hS).2.2.2
  have hcore : ∀ q ∈ H, ∀ S ∈ family q, core S ⊆ Window N d B V q := by
    intro q hq S hS
    obtain ⟨hSF, heq⟩ := hmem q S hS
    simpa only [heq] using (hw S hSF).1
  have hdis : ∀ q ∈ H, ∀ S ∈ family q, ∀ R ∈ family q, S ≠ R →
      Disjoint (S\core S) (R\core R) := by
    intro q hq S hS R hR hne
    obtain ⟨hSF, hSq⟩ := hmem q S hS
    obtain ⟨hRF, hRq⟩ := hmem q R hR
    exact hrem S hSF R hRF hne (hSq.trans hRq.symm)
  have hcross : ∀ q ∈ H, ∀ t ∈ H, ∀ S ∈ family q, ∀ R ∈ family t,
      (S∩R).Nonempty := by
    intro q hq t ht S hS R hR
    have hs := (hmem q S hS).1
    have hr := (hmem t R hR).1
    by_cases heq : S=R
    · subst R
      have hn : S.Nonempty := Finset.card_pos.mp (by have := hlow S hs; omega)
      simpa only [Finset.inter_self] using hn
    · exact isAP_nonempty (hF.2 S hs R hr heq)
  have hsize : ∀ q ∈ H, ∀ S ∈ family q, S.card ≤ theta q := by
    intro q hq S hS
    obtain ⟨hSF, heq⟩ := hmem q S hS
    have hm := (BandGeometry208.actual_traits hF hd hT hET start hbad hlow hhigh hsmall hsub S hSF).1
    have hc : S.card=MaxAPSize S+Defect S := by
      have hh := maxAPSize_le_card S
      unfold Defect
      omega
    have hp := (PhaseGeometry82427.actual_source_cap hd (by omega : 0 < B)
      (by omega : 0 < MaxAPSize S) (hsmall S hSF) hc (hsub S hSF) (hF.1 S hSF)).2
    dsimp only [theta, Cap, Swap]
    rw [←heq]
    exact le_min (by have hh := hhigh S hSF; dsimp only [V]; omega) hp
  have hwindow : ∀ q ∈ H, (Window N d B V q).card ≤ theta q := by
    intro q hq
    exact cap_window hd (by omega : 1 ≤ E) q
  have hheavy : ∀ q ∈ H, theta q < (family q).card := by
    intro q hq
    exact (Finset.mem_filter.mp hq).2
  have hpair : ∀ q ∈ H, ∀ t ∈ H, q.2=t.2 → theta t ≤ theta q →
      (Window N d B V q ∩ Window N d B V t).Nonempty := by
    intro q hq t ht hr horder
    have hst : ∀ S ∈ family t, S.card ≤ theta q :=
      fun S hS => (hsize t ht S hS).trans horder
    have hwt : (Window N d B V q).card < (family t).card :=
      (same_block_window_cap hd hE (hres q hq) (hres t ht) hr).trans_lt (hheavy t ht)
    exact heavy_core_pools_intersect core (hcore q hq) (hcore t ht)
      (hdis q hq) (hdis t ht) (hcross q hq t ht) hst (hheavy q hq) hwt
  refine ⟨hres, ?_, hfeasible, ?_⟩
  · intro q hq t ht hr
    by_cases horder : theta t ≤ theta q
    · exact fixed_block_window_eq hd (hres q hq) (hres t ht) rfl hr.symm
        (hpair q hq t ht hr horder)
    · exact (fixed_block_window_eq hd (hres t ht) (hres q hq) rfl hr
        (hpair t ht q hq hr.symm (by omega))).symm
  · intro q hq hqO t ht htO
    have hordinary : ∀ u ∈ H, V-E+u.2*B ≤ N/d → V-1 ≤ theta u := by
      intro u hu ho
      exact ordinary_cap hd (hres u hu) hEV ho
    have hmeet : ∀ u ∈ H, V-E+u.2*B ≤ N/d → ∀ z ∈ H,
        theta u ≤ theta z → (Window N d B V u ∩ Window N d B V z).Nonempty := by
      intro u hu ho z hz horder
      have hst : ∀ S ∈ family z, S.card ≤ theta u := by
        intro S hS
        have hh := hhigh S (hmem z S hS).1
        exact (show S.card ≤ U-1 by omega).trans (hUV.trans (hordinary u hu ho))
      have hwt := (hwindow u hu).trans horder |>.trans_lt (hheavy z hz)
      exact heavy_core_pools_intersect core (hcore u hu) (hcore z hz)
        (hdis u hu) (hdis z hz) (hcross u hu z hz) hst (hheavy u hu) hwt
    by_cases horder : theta q ≤ theta t
    · exact hmeet q hq hqO t ht horder
    · simpa only [Finset.inter_comm] using hmeet t ht htO q hq (by omega)

#print axioms actual_properties
end
end JSP233.PhaseProperties82427
