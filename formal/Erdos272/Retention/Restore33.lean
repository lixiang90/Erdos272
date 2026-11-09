module

public import Erdos272.Retention.ThinFringe33
public import Erdos272.Retention.KKRetention32

@[expose] public section

/-! Actual thin-fringe deletion and recovery. The retained-family exact
bound remains an explicit premise; no global reduction is asserted. -/
namespace JSP233.Restore33
open StarCompletion ThinFringe33 KKRetention32
open scoped Classical
noncomputable section

theorem retained_interval_geometry (N t : ℕ) (F G E : Finset (Finset ℤ)) (L R : ℤ)
    (hG : G=F\E) (hlegal : Legal (Ground N) F)
    (hcoreG : ∃ H∈G, IsAP H ∧ Finset.Icc L R⊆H)
    (ht : (t:ℤ)=L+(N:ℤ)-R) (hthin : 256*t≤N) :
    1≤L ∧ L≤R ∧ R≤(N:ℤ) ∧ ∃ H∈F, IsAP H ∧ Finset.Icc L R⊆H := by
  obtain ⟨H,hHG,hAP,hIH⟩ := hcoreG
  have hHF : H∈F := by rw [hG] at hHG; exact (Finset.mem_sdiff.mp hHG).1
  have htN : (t:ℤ)≤(N:ℤ) := by exact_mod_cast (show t≤N by omega)
  have hLR : L≤R := by omega
  have hLmem : L∈H := hIH (Finset.mem_Icc.mpr ⟨le_rfl,hLR⟩)
  have hRmem : R∈H := hIH (Finset.mem_Icc.mpr ⟨hLR,le_rfl⟩)
  have hL := (mem_ground N L).mp (hlegal.1 H hHF hLmem)
  have hR := (mem_ground N R).mp (hlegal.1 H hHF hRmem)
  exact ⟨hL.1,hLR,hR.2,H,hHF,hAP,hIH⟩

theorem actual_deleted_fringe_quarter (N t J : ℕ) (F G E : Finset (Finset ℤ)) (L R : ℤ)
    (hN : 1≤N) (hJ : 19≤J) (hG : G=F\E) (hEF : E⊆F)
    (hlegal : Legal (Ground N) F) (hbad : ∀ S∈E, ¬IsAP S)
    (hdense : ∀ S∈E, N<16*S.card)
    (hcoreG : ∃ H∈G, IsAP H ∧ Finset.Icc L R⊆H)
    (ht : (t:ℤ)=L+(N:ℤ)-R) (hthin : 256*t*J≤N) :
    E.card≤(N-1)/4 := by
  have hp := Nat.mul_le_mul_left (256*t) (show 1≤J by omega)
  have hthin0 : 256*t≤N := by omega
  obtain ⟨hL,hLR,hR,hcoreF⟩ := retained_interval_geometry N t F G E L R hG hlegal hcoreG ht hthin0
  exact (actual_dense_fringe_bound_of_length N t F E L R hlegal hEF hbad hdense
    hL hLR hR hcoreF ht hthin0).trans (fringe_quarter_payment N t J hN hJ hthin)

theorem actual_thin_fringe_restore (N t J : ℕ) (F G E : Finset (Finset ℤ)) (L R : ℤ)
    (hN : 1≤N) (hJ : 19≤J) (hG : G=F\E) (hEF : E⊆F)
    (hlegal : Legal (Ground N) F) (hbad : ∀ S∈E, ¬IsAP S)
    (hdense : ∀ S∈E, N<16*S.card)
    (hcoreG : ∃ H∈G, IsAP H ∧ Finset.Icc L R⊆H)
    (ht : (t:ℤ)=L+(N:ℤ)-R) (hthin : 256*t*J≤N)
    (hGcard : G.card≤N.choose 2+1) : F.card≤B N := by
  have hE := actual_deleted_fringe_quarter N t J F G E L R hN hJ hG hEF hlegal hbad
    hdense hcoreG ht hthin
  have hc := deletion_card_exact F E hEF
  rw [←hG] at hc
  unfold B
  omega

#print axioms retained_interval_geometry
#print axioms actual_deleted_fringe_quarter
#print axioms actual_thin_fringe_restore
end
end JSP233.Restore33
