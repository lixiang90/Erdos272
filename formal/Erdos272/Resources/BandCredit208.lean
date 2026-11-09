module

public import Erdos272.Resources.BandLabels208

@[expose] public section

namespace JSP233.BandCredit208
open StarCompletion APGeometry NearAP36 ShiftedBlocks208 BandLabels208
open scoped Classical
noncomputable section
set_option maxHeartbeats 0

theorem actual_heavy_members {N d T E B U : ℕ} {F : Finset (Finset ℤ)} (a : Finset ℤ → ℕ)
    (hmap : ∀ S ∈ F, LightPhases208.Label a d B S ∈ LightPhases208.Indices N d (T-E) B)
    (S : Finset ℤ) :
    LightPhases208.Label a d B S ∈ LightPhases208.Heavy N d T E B (U+B-3) F a ↔
      Code d B (a S) ∈ BandSystem208.Heavy N d B U E F a := by
  rw [←actual_heavy_image a hmap]
  constructor
  · intro hh
    obtain ⟨q,hq,heq⟩ := Finset.mem_image.mp hh
    have he : q=Code d B (a S) := swap_injective (heq.trans (label_swap a d B S))
    simpa only [he] using hq
  · intro hh
    exact Finset.mem_image.mpr ⟨Code d B (a S),hh,(label_swap a d B S).symm⟩

theorem actual_heavy_family {N d T E B U : ℕ} {F : Finset (Finset ℤ)} (a : Finset ℤ → ℕ)
    (hmap : ∀ S ∈ F, LightPhases208.Label a d B S ∈ LightPhases208.Indices N d (T-E) B) :
    F.filter (fun S => LightPhases208.Label a d B S ∈ LightPhases208.Heavy N d T E B (U+B-3) F a)=
      F.filter (fun S => Code d B (a S) ∈ BandSystem208.Heavy N d B U E F a) := by
  ext S
  simp only [Finset.mem_filter,actual_heavy_members a hmap]

theorem actual_closed_credit {N d T E B U : ℕ} {F : Finset (Finset ℤ)}
    (a m e : Finset ℤ → ℕ) (hd : 0 < d) (hB : 0 < B)
    (hsize : ∀ S ∈ F, T ≤ S.card) (hTE : E < T) (hTV : T ≤ U+B-3)
    (hoff : ∀ S ∈ F, e S < E) (hcard : ∀ S ∈ F, S.card=m S+e S)
    (hsub : ∀ S ∈ F, Grid (a S) d (m S) ⊆ S)
    (hground : ∀ S ∈ F, S ⊆ Ground N) (hupper : ∀ S ∈ F, S.card ≤ U+B-3) :
    F.card+T*(BandSystem208.Heavy N d B U E F a).card ≤
      LightPrice208.Closed N d T E B (U+B-3)+
        (F.filter (fun S => Code d B (a S) ∈ BandSystem208.Heavy N d B U E F a)).card := by
  have hmap := LightPhases208.actual_label a m e hd hB hsize hTE hoff hcard hsub hground
  have hh := LightActualPrice208.actual_closed_credit a m e hd hB hsize hTE hTV
    hoff hcard hsub hground hupper
  rw [actual_heavy_card a hmap,actual_heavy_family a hmap] at hh
  exact hh

#print axioms actual_heavy_family
#print axioms actual_closed_credit
end
end JSP233.BandCredit208
