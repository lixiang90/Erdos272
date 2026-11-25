module

public import Erdos272.Counting.APTail208
public import Erdos272.Counting.UnitCount218

@[expose] public section

namespace JSP233.APQuotient80470
open StarCompletion APGeometry APCount41 APTail208 HarmonicAbel29
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def Cost (n d : ℕ) : ℕ := (n/d)^2/4+n/d

def Tail (n : ℕ) : ℝ := ∑ d∈Finset.Icc 2 n, (Cost n d : ℝ)

theorem actual_step_span {N : ℕ} {S : Finset ℤ}
    (hS : S⊆Ground N) (hAP : IsAP S) (htwo : 2≤S.card) : Step S≤N-1 := by
  obtain ⟨_, p, hp⟩ := actual_step hAP
  obtain ⟨a, b, ha, had, _, _, _⟩ := apAt_adjacent_min hp htwo
  have hlo := (mem_ground N a).mp (hS ha)
  have hhi := (mem_ground N (a+(Step S : ℤ))).mp (hS had)
  omega

theorem rectangle_quotient (U V q : ℕ) (hsum : U+V≤q) :
    U*V+U+V≤q^2/4+q := by
  have hsumZ : (U : ℤ)+V≤q := by exact_mod_cast hsum
  have hquadZ : 4*(U : ℤ)*V≤(q : ℤ)^2 := by
    have hsum0 : (0 : ℤ)≤(U : ℤ)+V := by positivity
    have hq0 : (0 : ℤ)≤q := by positivity
    have hsquare := mul_le_mul hsumZ hsumZ hsum0 hq0
    have hskew := sq_nonneg ((U : ℤ)-V)
    nlinarith only [hsquare, hskew]
  have hquad : U*V*4≤q^2 := by
    have hh : 4*U*V≤q^2 := by exact_mod_cast hquadZ
    nlinarith only [hh]
  have hp := (Nat.le_div_iff_mul_le (by decide : 0<4)).mpr hquad
  omega

theorem actual_same_step_two_quotient {N d : ℕ} {F : Finset (Finset ℤ)}
    (hd : 0<d) (hlegal : Legal (Ground N) F)
    (htwo : ∀ S∈F, 2≤S.card)
    (hstep : ∀ S∈F, ∃ p : ℤ, APAt (d : ℤ) p S) :
    F.card≤Cost (N-1) d := by
  by_cases hF : F.Nonempty
  · have hne : ∀ S∈F, S.Nonempty := fun S hS =>
      Finset.card_pos.mp (by have ht := htwo S hS; omega)
    obtain ⟨c, hc, hroot⟩ := actual_same_step_common_root hF hlegal hne hstep
    have hnot : ({c} : Finset ℤ)∉F := by
      intro hmem
      have ht := htwo {c} hmem
      simp only [Finset.card_singleton] at ht
      omega
    let G := insert ({c} : Finset ℤ) F
    have hG : Legal (Ground N) G := legal_insert_common_singleton hc hlegal hroot
    have hGroot : ∀ S∈G, c∈S := by
      intro S hS
      rcases Finset.mem_insert.mp hS with rfl | hS
      · simp
      · exact hroot S hS
    have hGstep : ∀ S∈G, ∃ p : ℤ, APAt (d : ℤ) p S := by
      intro S hS
      rcases Finset.mem_insert.mp hS with rfl | hS
      · exact ⟨c, singleton_apAt hd c⟩
      · exact hstep S hS
    let U := (c-1).toNat/d
    let V := ((N : ℤ)-c).toNat/d
    have hb := actual_same_step_rectangle hd hc hG hGroot hGstep
    have hcard : G.card=F.card+1 := by
      dsimp only [G]
      exact Finset.card_insert_of_notMem hnot
    change G.card≤(U+1)*(V+1) at hb
    have hcN := (mem_ground N c).mp hc
    have hspan : (c-1).toNat+((N : ℤ)-c).toNat=N-1 := by omega
    have hu := Nat.div_mul_le_self (c-1).toNat d
    have hv := Nat.div_mul_le_self ((N : ℤ)-c).toNat d
    have hmul : (U+V)*d≤N-1 := by dsimp only [U, V]; nlinarith only [hu, hv, hspan]
    have hsum : U+V≤(N-1)/d := (Nat.le_div_iff_mul_le hd).mpr hmul
    have hproduct := rectangle_quotient U V ((N-1)/d) hsum
    dsimp only [Cost]
    rw [hcard] at hb
    nlinarith only [hb, hproduct]
  · have he : F=∅ := Finset.not_nonempty_iff_eq_empty.mp hF
    simp only [he, Finset.card_empty]
    exact Nat.zero_le _

theorem actual_tail_count {N : ℕ} {F : Finset (Finset ℤ)}
    (hlegal : Legal (Ground N) F) (hAP : ∀ S∈F, IsAP S)
    (htwo : ∀ S∈F, 2≤S.card) (hlarge : ∀ S∈F, 2≤Step S) :
    (F.card : ℝ)≤Tail (N-1) := by
  have hmaps : ∀ S∈F, Step S∈Finset.Icc 2 (N-1) := fun S hS =>
    Finset.mem_Icc.mpr ⟨hlarge S hS, actual_step_span (hlegal.1 S hS) (hAP S hS) (htwo S hS)⟩
  have hpart : (F.card : ℝ)=
      ∑ d∈Finset.Icc 2 (N-1), ((F.filter (fun S => Step S=d)).card : ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_fiberwise hmaps
  rw [hpart]
  unfold Tail
  apply Finset.sum_le_sum
  intro d hd
  have hsub : F.filter (fun S => Step S=d)⊆F := Finset.filter_subset _ _
  have hC : Legal (Ground N) (F.filter (fun S => Step S=d)) :=
    ⟨fun S hS => hlegal.1 S (hsub hS),
      fun S hS T hT hST => hlegal.2 S (hsub hS) T (hsub hT) hST⟩
  have hc := actual_same_step_two_quotient
    (by have hh := (Finset.mem_Icc.mp hd).1; omega : 0<d) hC
    (fun S hS => htwo S (hsub hS)) (by
      intro S hS
      obtain ⟨_, p, hp⟩ := actual_step (hAP S (hsub hS))
      exact ⟨p, by simpa only [(Finset.mem_filter.mp hS).2] using hp⟩)
  exact_mod_cast hc

theorem actual_AP_tail_partition {N : ℕ} {F : Finset (Finset ℤ)}
    (hlegal : Legal (Ground N) F) :
    ((F.filter IsAP).card : ℝ)≤(UnitCount218.UnitAP F).card+Tail (N-1)+1 := by
  let P := F.filter IsAP
  let A := P.filter fun S => 2≤S.card
  let C := P.filter fun S => ¬2≤S.card
  let D := A.filter fun S => ¬Step S=1
  let U := A.filter fun S => Step S=1
  have hPF : P⊆F := Finset.filter_subset _ _
  have hAF : A⊆F := (Finset.filter_subset _ _).trans hPF
  have hCF : C⊆F := (Finset.filter_subset _ _).trans hPF
  have hDF : D⊆F := (Finset.filter_subset _ _).trans hAF
  have hsub : ∀ G : Finset (Finset ℤ), G⊆F → Legal (Ground N) G := by
    intro G hGF
    exact ⟨fun S hS => hlegal.1 S (hGF hS),
      fun S hS T hT hST => hlegal.2 S (hGF hS) T (hGF hT) hST⟩
  have hDP : ∀ S∈D, IsAP S := fun S hS =>
    (Finset.mem_filter.mp ((Finset.filter_subset _ _).trans (Finset.filter_subset _ _) hS)).2
  have ht := actual_tail_count (hsub D hDF) hDP
    (fun S hS => (Finset.mem_filter.mp ((Finset.filter_subset _ _) hS)).2)
    (fun S hS => by
      have hp := (actual_step (hDP S hS)).1
      have he := (Finset.mem_filter.mp hS).2
      omega)
  have hs := actual_singleton_family_count (hsub C hCF)
    (fun S hS => by have hh := (Finset.mem_filter.mp hS).2; omega)
  have hU : U=UnitCount218.UnitAP F := by
    ext S
    simp only [U, A, P, UnitCount218.UnitAP, Finset.mem_filter]
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
  nlinarith only [ht, hpR, hqR, hsR]

#print axioms actual_step_span
#print axioms rectangle_quotient
#print axioms actual_same_step_two_quotient
#print axioms actual_tail_count
#print axioms actual_AP_tail_partition
end
end JSP233.APQuotient80470
