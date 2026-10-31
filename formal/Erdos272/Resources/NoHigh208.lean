import Erdos272.Resources.PreparedWitness48
import Mathlib.Tactic

/-! # Local codes for actual preparation failures

The first point above the cut is chosen inside the actual source. The
crooked-trace code retains the terminal half-open interval for its smaller
step. The older global `WitnessException` is not changed.
-/
namespace JSP233.NoHigh208
open StarCompletion APGeometry LongTerminal35 RestrictedWitness44 PreparedWitness48
open WitnessInterval43 PrivatePairExistence
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0

def Failure (F : Finset (Finset ℤ)) (c L : ℤ) : Finset (Finset ℤ) :=
  CrookedMembers F \ HighMembers F c L

def NoHighAt (S : Finset ℤ) (c L : ℤ) : Prop :=
  ∀ Q, IntrinsicPair c S Q → ∀ z ∈ Q, z < L

def FirstHigh (S : Finset ℤ) (L : ℤ) : ℤ :=
  if h : (S.filter (L ≤ ·)).Nonempty then (S.filter (L ≤ ·)).min' h else L

def CrookedFailure (F : Finset (Finset ℤ)) (c L : ℤ) : Finset (Finset ℤ) :=
  (Failure F c L).filter fun S => ¬IsAP (Trace S c (FirstHigh S L))

def APFailure (F : Finset (Finset ℤ)) (c L : ℤ) : Finset (Finset ℤ) :=
  (Failure F c L).filter fun S => IsAP (Trace S c (FirstHigh S L))

theorem failure_partition (F : Finset (Finset ℤ)) (c L : ℤ) :
    (CrookedFailure F c L).card + (APFailure F c L).card = (Failure F c L).card := by
  have h := Finset.card_filter_add_card_filter_not (s := Failure F c L)
    (fun S => IsAP (Trace S c (FirstHigh S L)))
  simpa only [CrookedFailure, APFailure, Nat.add_comm] using h

theorem failure_subset (F : Finset (Finset ℤ)) (c L : ℤ) : Failure F c L ⊆ F := by
  intro S hS
  exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp hS).1).1

theorem failure_no_high {F : Finset (Finset ℤ)} {S : Finset ℤ} {c L : ℤ}
    (hS : S ∈ Failure F c L) : NoHighAt S c L := by
  obtain ⟨hSC, hnot⟩ := Finset.mem_sdiff.mp hS
  intro Q hQ z hz
  by_contra hLz
  apply hnot
  exact Finset.mem_filter.mpr ⟨hSC, Q, hQ, z, hz, by omega⟩

theorem firstHigh_spec {S : Finset ℤ} {L : ℤ}
    (h : (S.filter (L ≤ ·)).Nonempty) :
    FirstHigh S L ∈ S ∧ L ≤ FirstHigh S L ∧
      ∀ z ∈ S, L ≤ z → FirstHigh S L ≤ z := by
  have hm := Finset.min'_mem (S.filter (L ≤ ·)) h
  obtain ⟨hmS, hLm⟩ := Finset.mem_filter.mp hm
  simp only [FirstHigh, dif_pos h]
  exact ⟨hmS, hLm, fun z hz hLz => Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨hz, hLz⟩)⟩

theorem failure_has_high {N : ℕ} {F : Finset (Finset ℤ)} {S P : Finset ℤ} {c L : ℤ}
    (hF : Legal (Ground N) F) (hroot : ∀ U ∈ F, ¬IsAP U → c ∈ U)
    (hP : P ∈ F) (hcP : c ∉ P) (hLP : ∀ z ∈ P, L ≤ z)
    (hS : S ∈ Failure F c L) : (S.filter (L ≤ ·)).Nonempty := by
  have hSF := failure_subset F c L hS
  have hbad := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hS).1).2
  have hcS := hroot S hSF hbad
  obtain ⟨z, hz⟩ := actual_avoider_meets_erase hF hSF hP hcS hcP
  obtain ⟨hzS, hzP⟩ := Finset.mem_inter.mp hz
  exact ⟨z, Finset.mem_filter.mpr ⟨(Finset.mem_erase.mp hzS).2, hLP z hzP⟩⟩

theorem failure_all_covered {N : ℕ} {F : Finset (Finset ℤ)} {S P : Finset ℤ} {c L : ℤ}
    (hF : Legal (Ground N) F) (hroot : ∀ U ∈ F, ¬IsAP U → c ∈ U)
    (hP : P ∈ F) (hcP : c ∉ P) (hLP : ∀ z ∈ P, L ≤ z) (hcL : c < L)
    (hS : S ∈ Failure F c L) : AllCovered S c (FirstHigh S L) := by
  have hhigh := failure_has_high hF hroot hP hcP hLP hS
  obtain ⟨hpS, hLp, _⟩ := firstHigh_spec hhigh
  have hSF := failure_subset F c L hS
  have hbad := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hS).1).2
  apply all_covered_of_no_witness_at (hroot S hSF hbad) hpS (by omega)
  intro x hW
  have hh := failure_no_high hS {FirstHigh S L, x} hW (FirstHigh S L) (by simp)
  omega

theorem segment_antitone {c p : ℤ} {d e : ℕ} (hde : d ∣ e) :
    Segment c p e ⊆ Segment c p d := by
  have hdeZ : (d : ℤ) ∣ (e : ℤ) := by exact_mod_cast hde
  intro x hx
  obtain ⟨hxI, hdx⟩ := Finset.mem_filter.mp hx
  exact Finset.mem_filter.mpr ⟨hxI, hdeZ.trans hdx⟩

theorem segment_isAP (c p : ℤ) {d : ℕ} (hd : 0 < d) : IsAP (Segment c p d) := by
  refine ⟨(d : ℤ), c, by exact_mod_cast hd, min c p, max c p, ?_, ?_⟩
  · intro x
    simp only [Segment, Finset.mem_filter, Finset.mem_Icc, and_assoc]
  · exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨min_le_left _ _, le_max_left _ _⟩, by simp⟩

theorem incompatible_symm {S : Finset ℤ} {c p : ℤ} {d e : ℕ}
    (h : IncompatibleCode S c p d e) : IncompatibleCode S c p e d := by
  refine ⟨h.2.1, h.1, ?_⟩
  simpa only [Finset.union_comm] using h.2.2

theorem incompatible_ne {S : Finset ℤ} {c p : ℤ} {d e : ℕ}
    (hd : 0 < d) (h : IncompatibleCode S c p d e) : d ≠ e := by
  rintro rfl
  exact h.2.2 ⟨Segment c p d, segment_isAP c p hd, by simp, h.1⟩

theorem trace_code_sorted {S : Finset ℤ} {c p : ℤ}
    (hc : c ∈ S) (hcover : AllCovered S c p) (hbad : ¬IsAP (Trace S c p)) :
    ∃ d e : ℕ, 0 < d ∧ d < e ∧ d ∣ Distance c p ∧ e ∣ Distance c p ∧
      IncompatibleCode S c p d e := by
  obtain ⟨d, e, hd, he, hdd, hed, hcode⟩ := actual_incompatible_trace_code hc hcover hbad
  have hne := incompatible_ne hd hcode
  by_cases hde : d < e
  · exact ⟨d, e, hd, hde, hdd, hed, hcode⟩
  · exact ⟨e, d, he, by omega, hed, hdd, incompatible_symm hcode⟩

theorem incompatible_not_dvd {S : Finset ℤ} {c p : ℤ} {d e : ℕ}
    (hd : 0 < d) (h : IncompatibleCode S c p d e) : ¬d ∣ e := by
  intro hde
  apply h.2.2
  exact ⟨Segment c p d, segment_isAP c p hd,
    Finset.union_subset (Finset.Subset.refl _) (segment_antitone hde), h.1⟩

theorem terminal_step_window {S : Finset ℤ} {c L p : ℤ} {d : ℕ}
    (hcL : c < L) (hLp : L ≤ p) (hd : 0 < d) (hdiv : d ∣ Distance c p)
    (hseg : Segment c p d ⊆ S)
    (hfirst : ∀ z ∈ S, L ≤ z → p ≤ z) :
    Distance c p < (L - c).toNat + d := by
  have hcp : c < p := by omega
  have hD : 0 < Distance c p := Int.natAbs_pos.mpr (by omega)
  have hDn : (Distance c p : ℤ) = p - c := by
    simp only [Distance, Int.natAbs_of_nonneg (by omega : 0 ≤ p - c)]
  have hA : ((L - c).toNat : ℤ) = L - c := Int.toNat_of_nonneg (by omega)
  have hdZ : (0 : ℤ) < d := by exact_mod_cast hd
  have hdle : (d : ℤ) ≤ p - c := by
    have hh := Nat.le_of_dvd hD hdiv
    have hhZ : (d : ℤ) ≤ (Distance c p : ℤ) := by exact_mod_cast hh
    rwa [hDn] at hhZ
  have hdp : (d : ℤ) ∣ p - c := (nat_divides_distance_iff d c p).mp hdiv
  have hpmd : p - (d : ℤ) ∈ Segment c p d := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, ?_⟩
    · rw [min_eq_left hcp.le]; omega
    · rw [max_eq_right hcp.le]; omega
    · have hh := dvd_sub hdp (dvd_refl (d : ℤ))
      simpa only [show p - c - (d : ℤ) = p - (d : ℤ) - c by ring] using hh
  have hlow : p - (d : ℤ) < L := by
    by_contra h
    have hh := hfirst _ (hseg hpmd) (by omega)
    omega
  omega

theorem terminal_crooked_code {S : Finset ℤ} {c L p : ℤ}
    (hcS : c ∈ S) (hcL : c < L) (hpS : p ∈ S) (hLp : L ≤ p)
    (hfirst : ∀ z ∈ S, L ≤ z → p ≤ z)
    (hcover : AllCovered S c p) (hbad : ¬IsAP (Trace S c p)) :
    ∃ d e : ℕ, 0 < d ∧ d < e ∧ d ∣ Distance c p ∧ e ∣ Distance c p ∧
      ¬d ∣ e ∧ (L - c).toNat ≤ Distance c p ∧
      Distance c p < (L - c).toNat + d ∧ 3 * d ≤ Distance c p ∧
      2 * Distance c p < 3 * (L - c).toNat ∧ IncompatibleCode S c p d e := by
  obtain ⟨d, e, hd, hde, hdd, hed, hcode⟩ :=
    trace_code_sorted hcS hcover hbad
  have hnot := incompatible_not_dvd hd hcode
  have hn0 : 0 < Distance c p := Int.natAbs_pos.mpr (by omega)
  have hDn : (Distance c p : ℤ) = p - c := by
    simp only [Distance, Int.natAbs_of_nonneg (by omega : 0 ≤ p - c)]
  have hA : ((L - c).toNat : ℤ) = L - c := Int.toNat_of_nonneg (by omega)
  have hAn : (L - c).toNat ≤ Distance c p := by omega
  have hwindow := terminal_step_window hcL hLp hd hdd hcode.1 hfirst
  have henle := Nat.le_of_dvd hn0 hed
  have hen : e < Distance c p := by
    by_contra h
    have heq : e = Distance c p := by omega
    exact hnot (by simpa only [heq] using hdd)
  obtain ⟨r, hr⟩ := hed
  have hr2 : 2 ≤ r := by
    by_contra h
    have hcases : r = 0 ∨ r = 1 := by omega
    rcases hcases with rfl | rfl <;> nlinarith
  have hne2 : 2 * e ≤ Distance c p := by
    have hh := Nat.mul_le_mul_left e hr2
    nlinarith only [hh, hr]
  have hdd' := hdd
  obtain ⟨q, hq⟩ := hdd
  have hq3 : 3 ≤ q := by
    by_contra h
    have hcases : q = 0 ∨ q = 1 ∨ q = 2 := by omega
    rcases hcases with rfl | rfl | rfl <;> nlinarith
  have hd3 : 3 * d ≤ Distance c p := by
    have hh := Nat.mul_le_mul_left d hq3
    nlinarith only [hh, hq]
  exact ⟨d, e, hd, hde, hdd', by rw [hr]; exact dvd_mul_right e r, hnot, hAn,
    hwindow, hd3, by omega, hcode⟩

def TerminalCodes (A : ℕ) : Finset (Σ _ : ℕ, ℕ × ℕ) :=
  (Finset.Icc 1 (2 * A)).sigma fun n =>
    (n.divisors.product n.divisors).filter fun de =>
      0 < de.1 ∧ de.1 < de.2 ∧ ¬de.1 ∣ de.2 ∧
        A ≤ n ∧ n < A + de.1 ∧ 3 * de.1 ≤ n ∧ 2 * n < 3 * A

/-- Keeping the terminal half-open interval makes the anchor unique once
its smaller step is fixed. -/
theorem terminal_anchor_unique {A d n m : ℕ} (hd : 0 < d)
    (hdn : d ∣ n) (hdm : d ∣ m) (hAn : A ≤ n) (hAm : A ≤ m)
    (hn : n < A + d) (hm : m < A + d) : n = m := by
  obtain ⟨q, rfl⟩ := hdn
  obtain ⟨r, rfl⟩ := hdm
  by_cases hqr : q = r
  · rw [hqr]
  by_cases hlt : q < r
  · have hh := Nat.mul_le_mul_left d (show q + 1 ≤ r by omega)
    nlinarith only [hAn, hm, hh]
  · have hh := Nat.mul_le_mul_left d (show r + 1 ≤ q by omega)
    nlinarith only [hAm, hn, hh]

theorem terminal_step_small {A n d : ℕ} (hwin : n < A + d) (hthree : 3 * d ≤ n) :
    2 * d < A := by omega

/-- The original family's privacy proves injectivity into the local
terminal code pool. Sources may extend throughout the original ground. -/
theorem actual_crooked_first_count {Ω : Finset ℤ} {F : Finset (Finset ℤ)} {c L : ℤ}
    (hF : Legal Ω F) (hc : ∀ S ∈ F, c ∈ S) (hcL : c < L)
    (p : {S // S ∈ F} → ℤ)
    (hp : ∀ S, p S ∈ S.val ∧ L ≤ p S ∧ ∀ z ∈ S.val, L ≤ z → p S ≤ z)
    (hcover : ∀ S, AllCovered S.val c (p S))
    (hbad : ∀ S, ¬IsAP (Trace S.val c (p S))) :
    F.card ≤ (TerminalCodes (L - c).toNat).card := by
  let X := {S // S ∈ F}
  have hex : ∀ S : X, ∃ d e : ℕ, 0 < d ∧ d < e ∧ d ∣ Distance c (p S) ∧
      e ∣ Distance c (p S) ∧ ¬d ∣ e ∧ (L - c).toNat ≤ Distance c (p S) ∧
      Distance c (p S) < (L - c).toNat + d ∧ 3 * d ≤ Distance c (p S) ∧
      2 * Distance c (p S) < 3 * (L - c).toNat ∧ IncompatibleCode S.val c (p S) d e :=
    fun S => terminal_crooked_code (hc S.val S.property) hcL (hp S).1 (hp S).2.1
      (hp S).2.2 (hcover S) (hbad S)
  choose d e hd hde hdd hed hnot hAn hwindow hd3 hbound hcode using hex
  let f : X → (Σ _ : ℕ, ℕ × ℕ) := fun S => ⟨Distance c (p S), d S, e S⟩
  have hm : Set.MapsTo f (↑(Finset.univ : Finset X) : Set X) (TerminalCodes (L - c).toNat) := by
    intro S _
    have hn0 : Distance c (p S) ≠ 0 := Int.natAbs_ne_zero.mpr (by have hh := (hp S).2.1; omega)
    have hn1 : 1 ≤ Distance c (p S) := by omega
    have hnup : Distance c (p S) ≤ 2 * (L - c).toNat := by
      have hh := hbound S
      omega
    dsimp only [f, TerminalCodes]
    apply Finset.mem_sigma.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨hn1, hnup⟩, ?_⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨Nat.mem_divisors.mpr ⟨hdd S, hn0⟩,
      Nat.mem_divisors.mpr ⟨hed S, hn0⟩⟩, hd S, hde S, hnot S, hAn S,
      hwindow S, hd3 S, hbound S⟩
  have hi : Function.Injective f := by
    intro S T heq
    have hn : Distance c (p S) = Distance c (p T) := congrArg Sigma.fst heq
    have hdST : d S = d T := congrArg (fun q : Σ _ : ℕ, ℕ × ℕ => q.2.1) heq
    have heST : e S = e T := congrArg (fun q : Σ _ : ℕ, ℕ × ℕ => q.2.2) heq
    have hpST : p S = p T := distance_side_injective hn (by
      have hs := (hp S).2.1; have ht := (hp T).2.1
      simp only [decide_eq_true (by omega : c ≤ p S), decide_eq_true (by omega : c ≤ p T)])
    apply Subtype.ext
    exact actual_trace_code_private hF S.property T.property (hcode S)
      (by simpa only [hpST, hdST] using (hcode T).1)
      (by simpa only [hpST, heST] using (hcode T).2.1)
  have hh := Finset.card_le_card_of_injOn f hm hi.injOn
  simpa only [Finset.card_univ, X, Fintype.card_coe] using hh

theorem actual_failure_crooked_count {N : ℕ} {F : Finset (Finset ℤ)} {P : Finset ℤ} {c L : ℤ}
    (hF : Legal (Ground N) F) (hroot : ∀ S ∈ F, ¬IsAP S → c ∈ S)
    (hP : P ∈ F) (hcP : c ∉ P) (hLP : ∀ z ∈ P, L ≤ z) (hcL : c < L) :
    (CrookedFailure F c L).card ≤ (TerminalCodes (L - c).toNat).card := by
  let C := CrookedFailure F c L
  have hCfail : C ⊆ Failure F c L := Finset.filter_subset _ _
  have hCF : C ⊆ F := hCfail.trans (failure_subset F c L)
  have hlegal : Legal (Ground N) C := ⟨fun S hS => hF.1 S (hCF hS),
    fun S hS T hT hne => hF.2 S (hCF hS) T (hCF hT) hne⟩
  have hc : ∀ S ∈ C, c ∈ S := by
    intro S hS
    have hbad := (Finset.mem_filter.mp (Finset.mem_sdiff.mp (hCfail hS)).1).2
    exact hroot S (hCF hS) hbad
  apply actual_crooked_first_count hlegal hc hcL (fun S => FirstHigh S.val L)
  · intro S
    exact firstHigh_spec (failure_has_high hF hroot hP hcP hLP (hCfail S.property))
  · intro S
    exact failure_all_covered hF hroot hP hcP hLP hcL (hCfail S.property)
  · intro S
    exact (Finset.mem_filter.mp S.property).2

/-- In the AP-trace branch the witness adjacent to the root always points
to the right, because the actual first high point is to its right. -/
theorem positive_AP_trace_witness {S : Finset ℤ} {c p : ℤ}
    (hc : c ∈ S) (hp : p ∈ S) (hcp : c < p) (hbad : ¬IsAP S)
    (hcover : AllCovered S c p) (hAP : IsAP (Trace S c p)) :
    ∃ d : ℕ, 0 < d ∧ ∃ z : ℤ, IntrinsicPair c S {c + (d : ℤ), z} ∧
      d ∣ Distance c z := by
  obtain ⟨d, hd, hdd, hT, hgrid⟩ := actual_AP_trace_forces_grid hc hp (by omega) hcover hAP
  have hdZ : (0 : ℤ) < d := by exact_mod_cast hd
  have hD : (d : ℤ) ≤ p - c := by
    have hh := Nat.le_of_dvd (Int.natAbs_pos.mpr (by omega : p - c ≠ 0)) hdd
    have hhZ : (d : ℤ) ≤ (Distance c p : ℤ) := by exact_mod_cast hh
    simpa only [Distance, Int.natAbs_of_nonneg (by omega : 0 ≤ p - c)] using hhZ
  have hcT : c ∈ Trace S c p := Finset.mem_inter.mpr ⟨hc,
    Finset.mem_Icc.mpr ⟨min_le_left _ _, le_max_left _ _⟩⟩
  have hpT : p ∈ Trace S c p := Finset.mem_inter.mpr ⟨hp,
    Finset.mem_Icc.mpr ⟨min_le_right _ _, le_max_right _ _⟩⟩
  have hseg : c + (d : ℤ) ∈ Segment c p d := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, by simp⟩
    · rw [min_eq_left hcp.le]; omega
    · rw [max_eq_right hcp.le]; omega
  have ha : c + (d : ℤ) ∈ S :=
    (Finset.mem_inter.mp (actual_segment_subset_AP hT hcT hpT hseg)).1
  have hnear : ∀ y ∈ S, c < y → c + (d : ℤ) ≤ y := by
    intro y hy hcy
    have hh := Int.le_of_dvd (by omega : 0 < y - c)
      ((nat_divides_distance_iff d c y).mp (hgrid y hy))
    omega
  obtain ⟨z, hz⟩ := actual_right_neighbor_witness hc hbad ha (by omega) hnear
  exact ⟨d, hd, z, hz, hgrid z (hz.2.2.1 (by simp))⟩

/-- The low code coordinate is an actual private witness point. The whole
source remains in `Ground N`; it is never replaced by a shorter ground. -/
theorem actual_AP_first_count {N : ℕ} {F : Finset (Finset ℤ)} {c L : ℤ}
    (hF : Legal (Ground N) F) (hc : ∀ S ∈ F, c ∈ S)
    (hbad : ∀ S ∈ F, ¬IsAP S) (hcL : c < L)
    (hno : ∀ S ∈ F, NoHighAt S c L)
    (p : {S // S ∈ F} → ℤ) (hp : ∀ S, p S ∈ S.val ∧ L ≤ p S)
    (hcover : ∀ S, AllCovered S.val c (p S))
    (hAP : ∀ S, IsAP (Trace S.val c (p S))) :
    F.card ≤ ∑ z ∈ Finset.Icc 1 (L - 1), (Distance c z).divisors.card := by
  let X := {S // S ∈ F}
  have hex : ∀ S : X, ∃ d : ℕ, 0 < d ∧ ∃ z : ℤ,
      IntrinsicPair c S.val {c + (d : ℤ), z} ∧ d ∣ Distance c z := by
    intro S
    exact positive_AP_trace_witness (hc S.val S.property) (hp S).1 (by have hh := (hp S).2; omega)
      (hbad S.val S.property) (hcover S) (hAP S)
  choose d hd z hW hdiv using hex
  let U : Finset (Σ _ : ℤ, ℕ) :=
    (Finset.Icc 1 (L - 1)).sigma fun z => (Distance c z).divisors
  let f : X → (Σ _ : ℤ, ℕ) := fun S => ⟨z S, d S⟩
  have hm : Set.MapsTo f (↑(Finset.univ : Finset X) : Set X) U := by
    intro S _
    have hzS : z S ∈ S.val := (hW S).2.2.1 (by simp)
    have hzG := (mem_ground N (z S)).mp (hF.1 S.val S.property hzS)
    have hzL := hno S.val S.property _ (hW S) (z S) (by simp)
    have hzc : z S ≠ c := by
      intro he
      exact (hW S).2.1 (by simp [he])
    have hDn : Distance c (z S) ≠ 0 := Int.natAbs_ne_zero.mpr (sub_ne_zero.mpr hzc)
    have hzup : z S ≤ L - 1 := by omega
    exact Finset.mem_sigma.mpr ⟨Finset.mem_Icc.mpr ⟨hzG.1, hzup⟩,
      Nat.mem_divisors.mpr ⟨hdiv S, hDn⟩⟩
  have hi : Function.Injective f := by
    intro S T heq
    have hz : z S = z T := congrArg Sigma.fst heq
    have hdST : d S = d T := congrArg (fun q : Σ _ : ℤ, ℕ => q.2) heq
    apply Subtype.ext
    apply actual_intrinsic_member_eq hF S.property T.property (hc S.val S.property)
      (hc T.val T.property) (hW S)
    rw [hdST, hz]
    exact (hW T).2.2.1
  have hh := Finset.card_le_card_of_injOn f hm hi.injOn
  simpa only [Finset.card_univ, X, U, Fintype.card_coe, Finset.card_sigma] using hh

theorem actual_failure_AP_count {N : ℕ} {F : Finset (Finset ℤ)} {P : Finset ℤ} {c L : ℤ}
    (hF : Legal (Ground N) F) (hroot : ∀ S ∈ F, ¬IsAP S → c ∈ S)
    (hP : P ∈ F) (hcP : c ∉ P) (hLP : ∀ z ∈ P, L ≤ z) (hcL : c < L) :
    (APFailure F c L).card ≤ ∑ z ∈ Finset.Icc 1 (L - 1), (Distance c z).divisors.card := by
  let C := APFailure F c L
  have hCfail : C ⊆ Failure F c L := Finset.filter_subset _ _
  have hCF : C ⊆ F := hCfail.trans (failure_subset F c L)
  have hlegal : Legal (Ground N) C := ⟨fun S hS => hF.1 S (hCF hS),
    fun S hS T hT hne => hF.2 S (hCF hS) T (hCF hT) hne⟩
  have hbad : ∀ S ∈ C, ¬IsAP S := fun S hS =>
    (Finset.mem_filter.mp (Finset.mem_sdiff.mp (hCfail hS)).1).2
  have hc : ∀ S ∈ C, c ∈ S := fun S hS => hroot S (hCF hS) (hbad S hS)
  apply actual_AP_first_count hlegal hc hbad hcL
    (fun S hS => failure_no_high (hCfail hS)) (fun S => FirstHigh S.val L)
  · intro S
    have hh := firstHigh_spec (failure_has_high hF hroot hP hcP hLP (hCfail S.property))
    exact ⟨hh.1, hh.2.1⟩
  · intro S
    exact failure_all_covered hF hroot hP hcP hLP hcL (hCfail S.property)
  · intro S
    exact (Finset.mem_filter.mp S.property).2

theorem actual_failure_local_count {N : ℕ} {F : Finset (Finset ℤ)} {P : Finset ℤ} {c L : ℤ}
    (hF : Legal (Ground N) F) (hroot : ∀ S ∈ F, ¬IsAP S → c ∈ S)
    (hP : P ∈ F) (hcP : c ∉ P) (hLP : ∀ z ∈ P, L ≤ z) (hcL : c < L) :
    (Failure F c L).card ≤ (TerminalCodes (L - c).toNat).card +
      ∑ z ∈ Finset.Icc 1 (L - 1), (Distance c z).divisors.card := by
  have hC := actual_failure_crooked_count hF hroot hP hcP hLP hcL
  have hA := actual_failure_AP_count hF hroot hP hcP hLP hcL
  have hp := failure_partition F c L
  omega

#print axioms failure_all_covered
#print axioms terminal_crooked_code
#print axioms terminal_anchor_unique
#print axioms actual_crooked_first_count
#print axioms actual_failure_crooked_count
#print axioms positive_AP_trace_witness
#print axioms actual_AP_first_count
#print axioms actual_failure_local_count
end
end JSP233.NoHigh208
