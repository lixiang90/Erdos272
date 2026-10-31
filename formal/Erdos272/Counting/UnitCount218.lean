import Erdos272.Counting.PairShadowBudget218
import Erdos272.Counting.APTail208
import Erdos272.Resources.DenseDeletion208

namespace JSP233.UnitCount218
open StarCompletion APGeometry APCount41 APTail208 HarmonicAbel29
open DenseDeletion40 WitnessInterval43 PairShadowBudget218
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

def UnitAP (F : Finset (Finset ℤ)) : Finset (Finset ℤ) :=
  F.filter fun S => IsAP S ∧ 2≤S.card ∧ Step S=1

def AvoidUnitAP (F : Finset (Finset ℤ)) (c : ℤ) : Finset (Finset ℤ) :=
  (UnitAP F).filter fun S => c∉S

theorem unit_partition (F : Finset (Finset ℤ)) (c : ℤ) :
    (RootUnitAP F c).card+(AvoidUnitAP F c).card=(UnitAP F).card := by
  have he : (UnitAP F).filter (fun S => c∈S)=RootUnitAP F c := by
    ext S
    simp only [UnitAP,RootUnitAP,Finset.mem_filter]
    tauto
  rw [←he]
  exact Finset.card_filter_add_card_filter_not (s := UnitAP F) (fun S => c∈S)

theorem actual_AP_count {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 1≤N) (hF : Legal (Ground N) F) :
    ((F.filter IsAP).card : ℝ) ≤ (UnitAP F).card+
      (129/800 : ℝ)*(N : ℝ)^2+(N : ℝ)*(Harmonic N-1)+1 := by
  let P := F.filter IsAP
  let A := P.filter fun S => 2≤S.card
  let C := P.filter fun S => ¬2≤S.card
  let D := A.filter fun S => ¬Step S=1
  let U := A.filter fun S => Step S=1
  have hPF : P⊆F := Finset.filter_subset _ _
  have hAF : A⊆F := (Finset.filter_subset _ _).trans hPF
  have hCF : C⊆F := (Finset.filter_subset _ _).trans hPF
  have hDF : D⊆F := (Finset.filter_subset _ _).trans hAF
  have hsub : ∀G : Finset (Finset ℤ), G⊆F → Legal (Ground N) G := by
    intro G hGF
    exact ⟨fun S hS => hF.1 S (hGF hS),fun S hS T hT hn => hF.2 S (hGF hS) T (hGF hT) hn⟩
  have hDP : ∀S∈D, IsAP S := fun S hS =>
    (Finset.mem_filter.mp ((Finset.filter_subset _ _).trans (Finset.filter_subset _ _) hS)).2
  have ht := APTail208.actual_large_step_count hN (hsub D hDF) hDP
    (fun S hS => (Finset.mem_filter.mp ((Finset.filter_subset _ _) hS)).2)
    (fun S hS => by
      have hp := (actual_step (hDP S hS)).1
      have he := (Finset.mem_filter.mp hS).2
      omega)
  have hs := actual_singleton_family_count (hsub C hCF)
    (fun S hS => by have hh := (Finset.mem_filter.mp hS).2; omega)
  have hU : U=UnitAP F := by
    ext S
    simp only [U,A,P,UnitAP,Finset.mem_filter]
    tauto
  have hp := Finset.card_filter_add_card_filter_not (s := P) (fun S => 2≤S.card)
  have hq := Finset.card_filter_add_card_filter_not (s := A) (fun S => Step S=1)
  change A.card+C.card=P.card at hp
  change U.card+D.card=A.card at hq
  have hpR : (A.card : ℝ)+C.card=P.card := by exact_mod_cast hp
  have hqR : (U.card : ℝ)+D.card=A.card := by exact_mod_cast hq
  have hsR : (C.card : ℝ)≤1 := by exact_mod_cast hs
  rw [hU] at hqR
  change (P.card : ℝ)≤_
  nlinarith only [ht,hpR,hqR,hsR]

theorem actual_avoiding_crooked_eq_omitted {N : ℕ} {F : Finset (Finset ℤ)} {c : ℤ}
    (hroot : ∀S∈Retained N 11 F,¬IsAP S→c∈S) :
    F.filter (fun S => ¬IsAP S ∧ c∉S)=TerminalDeficit51.OmittedAvoiders N 11 F c := by
  ext S
  constructor
  · intro hS
    obtain ⟨hSF,hbad,hcS⟩ := Finset.mem_filter.mp hS
    have hd : S∈Deleted N 11 F := by
      by_contra hnot
      exact hcS (hroot S (Finset.mem_sdiff.mpr ⟨hSF,hnot⟩) hbad)
    exact Finset.mem_filter.mpr ⟨hd,hcS⟩
  · intro hS
    obtain ⟨hSD,hcS⟩ := Finset.mem_filter.mp hS
    exact Finset.mem_filter.mpr ⟨actual_deleted_subset N 11 F hSD,
      (Finset.mem_filter.mp hSD).2.1,hcS⟩

theorem actual_family_partition {N : ℕ} {F : Finset (Finset ℤ)} {c : ℤ}
    (hroot : ∀S∈Retained N 11 F,¬IsAP S→c∈S) :
    (RootCrooked F c).card+(TerminalDeficit51.OmittedAvoiders N 11 F c).card+
      (F.filter IsAP).card=F.card := by
  let C := F.filter fun S => ¬IsAP S
  have h1 : C.filter (fun S => c∈S)=RootCrooked F c := by
    ext S
    simp only [C,RootCrooked,Finset.mem_filter]
    tauto
  have h2 : C.filter (fun S => ¬c∈S)=TerminalDeficit51.OmittedAvoiders N 11 F c := by
    rw [←actual_avoiding_crooked_eq_omitted hroot]
    ext S
    simp only [C,Finset.mem_filter]
    tauto
  have hc := Finset.card_filter_add_card_filter_not (s := C) (fun S => c∈S)
  rw [h1,h2] at hc
  have hf := Finset.card_filter_add_card_filter_not (s := F) IsAP
  change (F.filter IsAP).card+C.card=F.card at hf
  omega

theorem actual_unit_cap_of_shadow {N : ℕ} {F : Finset (Finset ℤ)} {c : ℤ}
    (hN : 10902≤N) (hc : c∈Ground N) (hF : Legal (Ground N) F)
    (hcard : B N≤F.card) (hroot : ∀S∈Retained N 11 F,¬IsAP S→c∈S)
    (hshadow : 2*((RootUnitAP F c).card : ℝ)-(5/2 : ℝ)*((N-1 : ℕ) : ℝ) ≤
      (PairShadow (RootUnitAP F c) c).card) :
    ((UnitAP F).card : ℝ) ≤ (129/800 : ℝ)*(N : ℝ)^2+
      2*(AvoidUnitAP F c).card+(Harmonic N+243/2)*(N : ℝ)+1933/2 := by
  have hp := actual_ground_root_unit_pair_capacity hc hF
  have hpR : ((RootCrooked F c).card : ℝ)+(PairShadow (RootUnitAP F c) c).card≤
      ((N-1).choose 2 : ℝ) := by exact_mod_cast hp
  have hAP := actual_AP_count (by omega : 1≤N) hF
  have hpart := actual_family_partition hroot
  have hpartR : ((RootCrooked F c).card : ℝ)+(TerminalDeficit51.OmittedAvoiders N 11 F c).card+
      (F.filter IsAP).card=F.card := by exact_mod_cast hpart
  have hup : ((RootUnitAP F c).card : ℝ)+(AvoidUnitAP F c).card=(UnitAP F).card := by
    exact_mod_cast unit_partition F c
  have he := DenseDeletion208.actual_omitted11_affine c hN hF
  have heR : ((TerminalDeficit51.OmittedAvoiders N 11 F c).card : ℝ)≤121*(N : ℝ)+968 := by
    exact_mod_cast he
  have hnear : (N.choose 2 : ℝ)+1≤F.card := by
    exact_mod_cast (show N.choose 2+1≤F.card by unfold B at hcard; omega)
  have hN1 : 1≤N := by omega
  have hncast : ((N-1 : ℕ) : ℝ)=(N : ℝ)-1 := by rw [Nat.cast_sub hN1]; norm_num
  have hchoose : ((N-1).choose 2 : ℝ)=((N : ℝ)-1)*((N : ℝ)-2)/2 := by
    rw [Nat.cast_choose_two,hncast]
    ring
  rw [hchoose] at hpR
  rw [Nat.cast_choose_two] at hnear
  rw [hncast] at hshadow
  nlinarith only [hshadow,hpR,hAP,hpartR,hup,heR,hnear]

#print axioms actual_AP_count
#print axioms actual_family_partition
#print axioms actual_unit_cap_of_shadow
end
end JSP233.UnitCount218
