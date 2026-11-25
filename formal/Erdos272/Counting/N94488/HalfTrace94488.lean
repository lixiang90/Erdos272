module

public import Erdos272.Retention.ThinFringe33
public import Erdos272.Resources.N291012.RootModel291012

@[expose] public section

namespace JSP233.HalfTrace94488
open StarCompletion APGeometry ThinFringe33 RootModel291012
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def Centre (L R : ℤ) : ℤ := L+(R-L)/2

theorem large_trace_central {L R : ℤ} {S : Finset ℤ}
    (hLR : L ≤ R) (hsub : S ⊆ Finset.Icc L R) (hAP : IsAP S)
    (hcard : R-L+2 < 2*(S.card : ℤ)) :
    APAt 1 (Centre L R) S ∧ Centre L R ∈ S ∧ Centre L R+1 ∈ S := by
  have htwo : 2 ≤ S.card := by omega
  obtain ⟨d, p, hp, _⟩ := (isAP_iff_exists_APAt S).mp hAP
  obtain ⟨a, b, ha, _had, hb, _hab, hspan⟩ := apAt_adjacent_min hp htwo
  have hLa := (Finset.mem_Icc.mp (hsub ha)).1
  have hbR := (Finset.mem_Icc.mp (hsub hb)).2
  have hd1 : d = 1 := by
    have hd := hp.1
    by_contra hne
    have hprod := mul_nonneg (show (0 : ℤ) ≤ d-2 by omega)
      (show (0 : ℤ) ≤ (S.card : ℤ)-1 by omega)
    nlinarith only [hprod, hspan, hLa, hbR, hcard]
  subst d
  have hau : a ≤ Centre L R := by dsimp only [Centre]; omega
  have hub : Centre L R+1 ≤ b := by dsimp only [Centre]; omega
  have hu : Centre L R ∈ S := apAt_fill hp ha hb hau (by omega) (one_dvd _)
  have hv : Centre L R+1 ∈ S := apAt_fill hp ha hb (by omega) hub (one_dvd _)
  exact ⟨apAt_rebase hp hu, hu, hv⟩

theorem actual_high_density_card {N L R : ℕ} {F E : Finset (Finset ℤ)}
    (hL : 1 ≤ L) (hLR : L ≤ R) (hRN : R ≤ N)
    (hF : Legal (Ground N) F) (hEF : E ⊆ F) (hbad : ∀ S ∈ E, ¬IsAP S)
    (hcore : ∃ H ∈ F, IsAP H ∧ Finset.Icc (L : ℤ) (R : ℤ) ⊆ H)
    (hdense : ∀ S ∈ E, ((N : ℝ)+Width N L R)/2 < S.card) :
    (E.card : ℝ) ≤ Width N L R-1 := by
  obtain ⟨H, hHF, hHAP, hIH⟩ := hcore
  have hout := ground_interval_exterior_card N (L := (L : ℤ)) (R := (R : ℤ))
    (by exact_mod_cast hL) (by exact_mod_cast hLR) (by exact_mod_cast hRN)
  have houtR : ((Ground N\Finset.Icc (L : ℤ) (R : ℤ)).card : ℝ) =
      (L : ℝ)+N-R-1 := by
    have hh : ((Ground N\Finset.Icc (L : ℤ) (R : ℤ)).card : ℝ) =
        (N : ℝ)-((R : ℝ)-L+1) := by exact_mod_cast hout
    linarith only [hh]
  have hgeom : ∀ S ∈ E,
      APAt 1 (Centre (L : ℤ) R) (S∩Finset.Icc (L : ℤ) (R : ℤ)) ∧
      Centre (L : ℤ) R ∈ S∩Finset.Icc (L : ℤ) (R : ℤ) ∧
      Centre (L : ℤ) R+1 ∈ S∩Finset.Icc (L : ℤ) (R : ℤ) := by
    intro S hS
    have hSH : S ≠ H := by intro he; exact hbad S hS (he.symm ▸ hHAP)
    obtain ⟨d, p, hp⟩ := apAt_interval_trace (hF.2 S (hEF hS) H hHF hSH) hIH
    have hc := card_le_trace_add_exterior (K := Finset.Icc (L : ℤ) (R : ℤ)) (hF.1 S (hEF hS))
    have hcR : (S.card : ℝ) ≤ (S∩Finset.Icc (L : ℤ) (R : ℤ)).card+
        (Ground N\Finset.Icc (L : ℤ) (R : ℤ)).card := by exact_mod_cast hc
    have hd := hdense S hS
    dsimp only [Width] at hd
    have hcardR : (R : ℝ)-L+2 < 2*((S∩Finset.Icc (L : ℤ) (R : ℤ)).card : ℝ) := by
      linarith only [hcR, houtR, hd]
    have hcard : (R : ℤ)-L+2 < 2*((S∩Finset.Icc (L : ℤ) (R : ℤ)).card : ℤ) := by
      exact_mod_cast hcardR
    have hne : (S∩Finset.Icc (L : ℤ) (R : ℤ)).Nonempty := by
      apply Finset.card_pos.mp
      have hLRZ : (L : ℤ) ≤ R := by exact_mod_cast hLR
      omega
    have hAP : IsAP (S∩Finset.Icc (L : ℤ) (R : ℤ)) :=
      by
        obtain ⟨x, hx⟩ := hne
        exact (isAP_iff_exists_APAt _).mpr ⟨d, x, apAt_rebase hp hx, hx⟩
    exact large_trace_central (by exact_mod_cast hLR) (Finset.inter_subset_right) hAP hcard
  have hb := actual_class_card_le_exterior
    (fun S hS => hF.1 S (hEF hS)) hbad
    (fun S hS T hT hST => hF.2 S (hEF hS) T (hEF hT) hST)
    (fun S hS => (hgeom S hS).1) (fun S hS => (hgeom S hS).2.1)
    (fun S hS => (hgeom S hS).2.2)
  have hbR : (E.card : ℝ) ≤ (Ground N\Finset.Icc (L : ℤ) (R : ℤ)).card := by
    exact_mod_cast hb
  dsimp only [Width]
  linarith only [hbR, houtR]

theorem actual_minimum_payment {N L R : ℕ} {F E : Finset (Finset ℤ)} {U : Finset ℤ}
    (hN : 160 ≤ N) (hL : 1 ≤ L) (hLR : L ≤ R) (hRN : R ≤ N)
    (hF : Legal (Ground N) F) (hEF : E ⊆ F) (hbad : ∀ S ∈ E, ¬IsAP S)
    (hcore : ∃ H ∈ F, IsAP H ∧ Finset.Icc (L : ℤ) (R : ℤ) ⊆ H)
    (hU : U ∈ E) (hmin : ∀ S ∈ E, U.card ≤ S.card)
    (hw : Width N L R ≤ (3/32 : ℝ)*N)
    (he : (E.card : ℝ) ≤ (13/2 : ℝ)*Width N L R-11/2) :
    4*(U.card : ℝ)+4*Width N L R+4*E.card+8 < 5*N := by
  have hn : (160 : ℝ) ≤ N := by exact_mod_cast hN
  have hsize : (U.card : ℝ) ≤ N := by
    exact_mod_cast (show U.card ≤ N by
      have hh := Finset.card_le_card (hF.1 U (hEF hU)); rwa [ground_card] at hh)
  by_cases hdense : ((N : ℝ)+Width N L R)/2 < U.card
  · have hd : ∀ S ∈ E, ((N : ℝ)+Width N L R)/2 < S.card := by
      intro S hS
      exact hdense.trans_le (by exact_mod_cast hmin S hS)
    have hb := actual_high_density_card hL hLR hRN hF hEF hbad hcore hd
    linarith only [hn, hw, hsize, hb]
  · have hd := le_of_not_gt hdense
    linarith only [hd, he, hw]

#print axioms large_trace_central
#print axioms actual_high_density_card
#print axioms actual_minimum_payment
end
end JSP233.HalfTrace94488
