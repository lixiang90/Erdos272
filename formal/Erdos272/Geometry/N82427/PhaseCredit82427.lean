module

public import Erdos272.Geometry.N82427.PhaseGeometry82427

@[expose] public section

namespace JSP233.PhaseCredit82427
open StarCompletion APGeometry NearAP36 ShiftedBlocks208 BandLabels208 PhaseDefs82427
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem actual_light_credit {N d T E B U : ℕ} {F : Finset (Finset ℤ)}
    (a m e : Finset ℤ → ℕ) (hd : 0 < d) (hB : 0 < B)
    (hsize : ∀ S ∈ F, T ≤ S.card) (hTE : E < T)
    (hoff : ∀ S ∈ F, e S < E) (hcard : ∀ S ∈ F, S.card=m S+e S)
    (hsub : ∀ S ∈ F, Grid (a S) d (m S) ⊆ S)
    (hground : ∀ S ∈ F, S ⊆ Ground N) (hupper : ∀ S ∈ F, S.card ≤ U+B-3) :
    F.card+T*(Heavy N d B U E F a).card ≤ Price N d T E B (U+B-3)+
      (F.filter (fun S => Code d B (a S) ∈ Heavy N d B U E F a)).card := by
  let I := F.image (fun S => Code d B (a S))
  let H := Heavy N d B U E F a
  let theta : (ℕ × ℕ) → ℕ := fun q => Cap N d E B (U+B-3) (Swap q)
  have hmap : ∀ S ∈ F, Code d B (a S) ∈ I :=
    fun S hS => Finset.mem_image.mpr ⟨S, hS, rfl⟩
  have hcap : ∀ S ∈ F, T ≤ theta (Code d B (a S)) := by
    intro S hS
    have hm : 0 < m S := by have := hsize S hS; have := hoff S hS; have := hcard S hS; omega
    have hp := (PhaseGeometry82427.actual_source_cap hd hB hm (hoff S hS)
      (hcard S hS) (hsub S hS) (hground S hS)).2
    exact (hsize S hS).trans (le_min (hupper S hS) hp)
  have hc := HeavyCredit208.actual_light_credit (fun S => Code d B (a S)) I H theta (fun _ => T)
    hmap (by
      intro q hq hnot
      have hh : ¬theta q < (F.filter (fun S => Code d B (a S)=q)).card := by
        intro h
        exact hnot (Finset.mem_filter.mpr ⟨hq, h⟩)
      omega) (by
      intro q hq hheavy
      obtain ⟨S, hS, heq⟩ := Finset.mem_image.mp hq
      simpa only [heq] using hcap S hS)
  have hcredit : (∑ q ∈ I, if q ∈ H then T else 0)=T*H.card := by
    have he : I.filter (fun q => q ∈ H)=H := by
      ext q
      simp only [Finset.mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨(Finset.mem_filter.mp h).1, h⟩⟩
    rw [←Finset.sum_filter, he]
    simp [Nat.mul_comm]
  rw [hcredit] at hc
  have hindices := LightPhases208.actual_label a m e hd hB hsize hTE hoff hcard hsub hground
  have hsubI : I.image Swap ⊆ LightPhases208.Indices N d (T-E) B := by
    intro q hq
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hr
    exact hindices S hS
  have hprice : (∑ q ∈ I, theta q) ≤ Price N d T E B (U+B-3) := by
    calc
      _ = ∑ i ∈ I.image Swap, Cap N d E B (U+B-3) i :=
        (Finset.sum_image (fun q hq t ht hqt => swap_injective hqt)).symm
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsubI (by intros; exact Nat.zero_le _)
  exact hc.trans (Nat.add_le_add_right hprice _)

#print axioms actual_light_credit
end
end JSP233.PhaseCredit82427
