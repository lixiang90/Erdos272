module

public import Erdos272.Resources.HeavyMenu208

@[expose] public section

namespace JSP233.BandSystem208
open StarCompletion APGeometry NearAP36 SourceBridge208 ShiftedBlocks208 ClippedWindows208
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0

def Fiber (F : Finset (Finset ℤ)) (d B : ℕ) (start : Finset ℤ → ℕ)
    (q : ℕ × ℕ) : Finset (Finset ℤ) := F.filter (fun S => Code d B (start S)=q)

def Heavy (N d B U E : ℕ) (F : Finset (Finset ℤ)) (start : Finset ℤ → ℕ) :
    Finset (ℕ × ℕ) := (F.image (fun S => Code d B (start S))).filter (fun q =>
      min (U+B-3) (N/d-q.2*B+E) < (Fiber F d B start q).card)

structure Properties (N d A B V E : ℕ) (H : Finset (ℕ × ℕ)) : Prop where
  residue : ∀ q ∈ H, q.1 < d
  injective : Set.InjOn Prod.snd (H : Set (ℕ × ℕ))
  feasible : ∀ q ∈ H, A+q.2*B ≤ N/d
  ordinary_pair : ∀ q ∈ H, V-E+q.2*B ≤ N/d → ∀ t ∈ H, V-E+t.2*B ≤ N/d →
    (Window N d B V q ∩ Window N d B V t).Nonempty

theorem actual_properties {N d T E U B : ℕ} {F : Finset (Finset ℤ)}
    (hF : Legal (Ground N) F) (hd : 0 < d) (hT : 2 ≤ T) (hET : E ≤ T)
    (hE : 1 ≤ E) (hTU : T < U) (hB : 2 ≤ B) (hBA : B ≤ T-E)
    (start : Finset ℤ → ℕ)
    (hbad : ∀ S ∈ F, ¬IsAP S) (hlow : ∀ S ∈ F, T ≤ S.card)
    (hhigh : ∀ S ∈ F, S.card < U) (hsmall : ∀ S ∈ F, Defect S < E)
    (hsub : ∀ S ∈ F, Grid (start S) d (MaxAPSize S) ⊆ S)
    (hgate : (StepClass208.PrimeGate d-1)*(T-E+1-B) ≥ E ∨
      StepClass208.PrimeGate d*B ≤ (StepClass208.PrimeGate d-1)*(T-E+1)) :
    Properties N d (T-E) B (U+B-3) E (Heavy N d B U E F start) := by
  let V := U+B-3
  let H := Heavy N d B U E F start
  let family := Fiber F d B start
  let core : Finset ℤ → Finset ℤ := fun S => Grid (start S) d (MaxAPSize S)
  let W : ℕ → ℕ := fun r => min V (N/d-r*B+E)
  have hEV : E < V := by dsimp [V]; omega
  have hw := BandGeometry208.actual_band_windows hF hd hT hET hB start hbad hlow hhigh hsmall hsub
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
    obtain ⟨S,hS,heq⟩ := himage q hq
    simpa only [heq] using (hw S hS).2.2.1
  have hfeasible : ∀ q ∈ H, T-E+q.2*B ≤ N/d := by
    intro q hq
    obtain ⟨S,hS,heq⟩ := himage q hq
    simpa only [heq] using (hw S hS).2.2.2
  have hcore : ∀ q ∈ H, ∀ S ∈ family q, core S ⊆ Window N d B V q := by
    intro q hq S hS
    obtain ⟨hSF,heq⟩ := hmem q S hS
    simpa only [heq] using (hw S hSF).1
  have hdis : ∀ q ∈ H, ∀ S ∈ family q, ∀ R ∈ family q, S ≠ R →
      Disjoint (S \ core S) (R \ core R) := by
    intro q hq S hS R hR hne
    obtain ⟨hSF,hSq⟩ := hmem q S hS
    obtain ⟨hRF,hRq⟩ := hmem q R hR
    exact hrem S hSF R hRF hne (hSq.trans hRq.symm)
  have hcross : ∀ q ∈ H, ∀ t ∈ H, ∀ S ∈ family q, ∀ R ∈ family t,
      (S ∩ R).Nonempty := by
    intro q hq t ht S hS R hR
    have hs := (hmem q S hS).1
    have hr := (hmem t R hR).1
    by_cases heq : S=R
    · subst R
      have hn : S.Nonempty := Finset.card_pos.mp (by have := hlow S hs; omega)
      simpa only [Finset.inter_self] using hn
    · exact isAP_nonempty (hF.2 S hs R hr heq)
  have hsize : ∀ q ∈ H, ∀ S ∈ family q, S.card ≤ W q.2 := by
    intro q hq S hS
    obtain ⟨hSF,heq⟩ := hmem q S hS
    simpa only [heq] using (hw S hSF).2.1
  have hwindow : ∀ q ∈ H, (Window N d B V q).card ≤ W q.2 := by
    intro q hq
    exact actual_clipped_threshold hd hE q
  have hheavy : ∀ q ∈ H, W q.2 < (family q).card := by
    intro q hq
    exact (Finset.mem_filter.mp hq).2
  have hi := RightWindows208.actual_right_injective hd family core W
    hres hcore hdis hcross hsize hwindow hheavy
  refine ⟨hres,hi,hfeasible,?_⟩
  intro q hq hqO t ht htO
  have hqW : W q.2=V := by
    dsimp [W]
    apply min_eq_left
    omega
  have htW : W t.2=V := by
    dsimp [W]
    apply min_eq_left
    omega
  have hst : ∀ S ∈ family t, S.card ≤ V := by
    intro S hS
    simpa only [htW] using hsize t ht S hS
  have hhq : V < (family q).card := by simpa only [hqW] using hheavy q hq
  have hht : (Window N d B V q).card < (family t).card := by
    have hwq : (Window N d B V q).card ≤ V := by simpa only [hqW] using hwindow q hq
    have hht : V < (family t).card := by simpa only [htW] using hheavy t ht
    exact hwq.trans_lt hht
  exact heavy_core_pools_intersect core (hcore q hq) (hcore t ht) (hdis q hq) (hdis t ht)
    (hcross q hq t ht) hst hhq hht

#print axioms actual_properties
end
end JSP233.BandSystem208
