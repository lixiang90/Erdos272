import Erdos272.Counting.ResidueRoot47
import Erdos272.Global.CrossStartup47
import Erdos272.Core.LinearOmitters43
import Erdos272.Counting.OutsideEnvelope43

/-! Actual all-cross-root exclusion and original-family one-sided reduction. -/
namespace JSP233.OneSided47
open StarCompletion APGeometry APCount41 Straddling47 CrossStartup47
open DenseDeletion40 FamilyReflect43 OutsideEnvelope43
open scoped Classical
noncomputable section

theorem actual_two_step_straddling_count {N : ℕ} {F : Finset (Finset ℤ)} {c : ℤ}
    (hcN : c∈Ground N) (hF : Legal (Ground N) F)
    (hroot : ∀ S∈F,¬IsAP S→c∈S)
    (hcross : ∀ S∈F,c∉S→StraddlesRoot c S)
    (hno : ¬LargeStepAvoider F c) (hout : ∃ P∈F,c∉P) :
    (F.card:ℝ)≤7*(N:ℝ)^2/16+3*N+1+6*(N:ℝ)*HarmonicAbel29.Harmonic N^3 := by
  obtain ⟨hdata,hO⟩ := actual_no_large_step_budget hF hroot hcross hno
  obtain ⟨P,hPF,hcP⟩ := hout
  have hPA : P∈Avoiders F c := Finset.mem_filter.mpr ⟨hPF,hcP⟩
  have hPP : P⊆OppositeParity N c := (hdata P hPA).2.2
  let R := RootPart F c
  have hRF : R⊆F := Finset.filter_subset _ _
  have hlegalR : Legal (Ground N) R :=
    ⟨fun S hS=>hF.1 S (hRF hS),fun S hS T hT hn=>hF.2 S (hRF hS) T (hRF hT) hn⟩
  have hrootR : Rooted R c := fun S hS=>(Finset.mem_filter.mp hS).2
  have hmet : ∀ S∈R,(S∩OppositeParity N c).Nonempty := by
    intro S hS
    have hcS := hrootR S hS
    have hSP : S≠P := by intro he; exact hcP (he ▸ hcS)
    obtain ⟨x,hx⟩ := isAP_nonempty (hF.2 S (hRF hS) P hPF hSP)
    obtain ⟨hxS,hxP⟩ := Finset.mem_inter.mp hx
    exact ⟨x,Finset.mem_inter.mpr ⟨hxS,hPP hxP⟩⟩
  have hR := ResidueRoot47.actual_rooted_parity_harmonic hcN hlegalR hrootR hmet
  have hpart : (R.card:ℝ)+(Avoiders F c).card=F.card := by
    exact_mod_cast root_avoider_card_partition F c
  linarith only [hR,hO,hpart]

theorem actual_two_step_straddling_gap {N : ℕ} {F : Finset (Finset ℤ)} {c : ℤ}
    (hN : 2^49≤N) (hcN : c∈Ground N) (hF : Legal (Ground N) F)
    (hroot : ∀ S∈F,¬IsAP S→c∈S)
    (hcross : ∀ S∈F,c∉S→StraddlesRoot c S)
    (hno : ¬LargeStepAvoider F c) (hout : ∃ P∈F,c∉P) :
    (F.card:ℝ)≤17*(N:ℝ)^2/36 := by
  let J := Nat.log 2 N+1
  obtain ⟨hJ,hNJ,hscale⟩ := actual_dyadic_cross_gate N hN
  change 50≤J at hJ
  change N<2^J at hNJ
  change 468*J^3≤N at hscale
  have hJR : (50:ℝ)≤J := by exact_mod_cast hJ
  have hH := HarmonicSharp39.actual_harmonic_tight N J hNJ
  have hH0 : 0≤HarmonicAbel29.Harmonic N := by
    unfold HarmonicAbel29.Harmonic
    exact Finset.sum_nonneg (fun _ _=>by positivity)
  have hHJ : HarmonicAbel29.Harmonic N≤J := by linarith only [hH,hJR]
  have hH3 : HarmonicAbel29.Harmonic N^3≤(J:ℝ)^3 := by gcongr
  have hJ3 : (1:ℝ)≤(J:ℝ)^3 := by
    have hp := mul_nonneg (show (0:ℝ)≤(J:ℝ)-1 by linarith only [hJR])
      (show (0:ℝ)≤(J:ℝ)^2+J+1 by positivity)
    nlinarith only [hp]
  have hbound := actual_two_step_straddling_count hcN hF hroot hcross hno hout
  have hlin := mul_le_mul_of_nonneg_left hJ3 (Nat.cast_nonneg (α:=ℝ) N)
  have hcube := mul_le_mul_of_nonneg_left hH3 (show (0:ℝ)≤6*(N:ℝ) by positivity)
  have hs : (468:ℝ)*(J:ℝ)^3≤N := by exact_mod_cast hscale
  have hsN := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg (α:=ℝ) N)
  have hn : (1:ℝ)≤N := by exact_mod_cast ((by norm_num : 1≤(2:ℕ)^49).trans hN)
  have hunit : (1:ℝ)≤(N:ℝ)*(J:ℝ)^3 := by nlinarith only [hlin,hn]
  nlinarith only [hbound,hlin,hcube,hsN,hunit]

theorem actual_all_cross_root_gap {N : ℕ} {F : Finset (Finset ℤ)} {c : ℤ}
    (hN : 2^49≤N) (hcN : c∈Ground N) (hF : Legal (Ground N) F)
    (hroot : ∀ S∈F,¬IsAP S→c∈S)
    (hcross : ∀ S∈F,c∉S→StraddlesRoot c S) (hout : ∃ P∈F,c∉P) :
    (F.card:ℝ)≤17*(N:ℝ)^2/36 := by
  by_cases hbig : LargeStepAvoider F c
  · obtain ⟨P,hP,hcP,d,hd,p,hAP⟩ := hbig
    obtain ⟨_,hNJ,hscale⟩ := actual_dyadic_cross_gate N hN
    exact NonIntervalAP47.actual_large_step_straddling_gap
      ((by norm_num : 6≤(2:ℕ)^49).trans hN) hNJ hscale hcN hF hroot hcross
      hP hcP (by exact_mod_cast hd) hAP
  · exact actual_two_step_straddling_gap hN hcN hF hroot hcross hbig hout

theorem actual_near_one_sided_reduction {N : ℕ} {F : Finset (Finset ℤ)} {c : ℤ}
    (hN : 2^49≤N) (hcN : c∈Ground N) (hF : Legal (Ground N) F)
    (hroot : ∀ S∈F,¬IsAP S→c∈S) (hnear : 17*(N:ℝ)^2/36<F.card) :
    Rooted F c ∨ ∃ P∈F,c∉P ∧ ((∀ x∈P,x<c) ∨ ∀ x∈P,c<x) := by
  by_cases hr : Rooted F c
  · exact Or.inl hr
  · apply Or.inr
    by_contra hn
    have hcross := actual_no_one_sided_cross hn
    have hout : ∃ P∈F,c∉P := by
      change ¬∀ P∈F,c∈P at hr
      push Not at hr
      exact hr
    have hb := actual_all_cross_root_gap hN hcN hF hroot hcross hout
    linarith only [hb,hnear]

theorem actual_original_one_sided_avoider28 {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 2^49≤N) (hF : Legal (Ground N) F) (hcounter : B N<F.card) :
    ∃ c∈Ground N,(∀ S∈Retained N 28 F,¬IsAP S→c∈S) ∧
      ∃ P∈Retained N 28 F,IsAP P ∧ c∉P ∧ ((∀ x∈P,x<c) ∨ ∀ x∈P,c<x) := by
  obtain ⟨c,hc,hroot,hnstar,hG,_,_⟩ :=
    LinearOmitters43.actual_original_nonstar_reduction28 hN hF hcounter
  have hs := actual_near_one_sided_reduction hN hc hG hroot
    (actual_retained_above_cross_gap28 hN hF hcounter)
  rcases hs with hr | ⟨P,hP,hcP,hside⟩
  · exact False.elim (hnstar ⟨c,hc,hr⟩)
  · refine ⟨c,hc,hroot,P,hP,?_,hcP,hside⟩
    by_contra hn
    exact hcP (hroot P hP hn)

theorem actual_original_right_avoider28 {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 2^49≤N) (hF : Legal (Ground N) F) (hcounter : B N<F.card) :
    ∃ H : Finset (Finset ℤ),(H=F ∨ H=Family N F) ∧ Legal (Ground N) H ∧ H.card=F.card ∧
      (Deleted N 28 H).card=(Deleted N 28 F).card ∧
      (Retained N 28 H).card=(Retained N 28 F).card ∧
      ∃ d∈Ground N,(∀ S∈Retained N 28 H,¬IsAP S→d∈S) ∧
        ∃ P∈Avoiders (Retained N 28 H) d,IsAP P ∧ ∀ x∈P,d<x := by
  obtain ⟨c,hc,hroot,P,hP,_hAP,hcP,hside⟩ := actual_original_one_sided_avoider28 hN hF hcounter
  obtain ⟨H,hHF,hLH,hcard,hD,hG,d,hd,hrootH,hcase⟩ :=
    actual_retained_right_orientation N 28 F c hF hc hroot (Or.inr ⟨P,hP,hcP,hside⟩)
  refine ⟨H,hHF,hLH,hcard,hD,hG,d,hd,hrootH,?_⟩
  rcases hcase with hstar | ⟨T,hT,hright⟩
  · have hb := LinearOmitters43.actual_retained_star_original_payment28 hN hd hLH hstar
    omega
  · refine ⟨T,hT,?_,hright⟩
    by_contra hn
    obtain ⟨hTF,hdT⟩ := Finset.mem_filter.mp hT
    exact hdT (hrootH T hTF hn)

theorem actual_original_outside_envelope28 {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 2^49≤N) (hF : Legal (Ground N) F) (hcounter : B N<F.card) :
    ∃ H : Finset (Finset ℤ),(H=F ∨ H=Family N F) ∧ Legal (Ground N) H ∧ H.card=F.card ∧
      (Deleted N 28 H).card=(Deleted N 28 F).card ∧
      (Retained N 28 H).card=(Retained N 28 F).card ∧
      ∃ d∈Ground N,(∀ S∈Retained N 28 H,¬IsAP S→d∈S) ∧
        (∀ S∈Avoiders (Retained N 28 H) d,IsAP S) ∧
        ∃ L R : ℕ,d<(L:ℤ) ∧ L≤R ∧ R≤N ∧
          (∃ P∈Avoiders (Retained N 28 H) d,∀ x∈P,(L:ℤ)≤x) ∧
          (∃ T∈Avoiders (Retained N 28 H) d,∀ x∈T,x≤(R:ℤ)) ∧
          ∀ S∈Avoiders (Retained N 28 H) d,
            (∃ a∈S,a≤(L:ℤ) ∧ ∀ x∈S,a≤x) ∧
            ∃ b∈S,(R:ℤ)≤b ∧ ∀ x∈S,x≤b := by
  obtain ⟨H,hHF,hLH,hcard,hD,hG,d,hd,hroot,P,hP,_hAP,hright⟩ :=
    actual_original_right_avoider28 hN hF hcounter
  have htwo : 2≤(Retained N 28 H).card := by
    rw [hG]
    exact actual_retained_card_two28 hN hF hcounter
  obtain ⟨L,R,hL,hLR,hRN,hPL,hTR,henv⟩ := actual_outside_member_envelope
    (actual_retained_legal hLH) htwo ⟨P,hP,hright⟩
  refine ⟨H,hHF,hLH,hcard,hD,hG,d,hd,hroot,?_,L,R,hL,hLR,hRN,hPL,hTR,henv⟩
  intro S hS
  obtain ⟨hSF,hdS⟩ := Finset.mem_filter.mp hS
  by_contra hn
  exact hdS (hroot S hSF hn)

#print axioms actual_two_step_straddling_count
#print axioms actual_two_step_straddling_gap
#print axioms actual_all_cross_root_gap
#print axioms actual_near_one_sided_reduction
#print axioms actual_original_one_sided_avoider28
#print axioms actual_original_right_avoider28
#print axioms actual_original_outside_envelope28
end
end JSP233.OneSided47
