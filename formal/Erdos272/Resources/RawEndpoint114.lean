module

public import Erdos272.Resources.RawEndpoint113
public import Erdos272.Retention.CeilFringe113
public import Erdos272.Counting.TerminalDeficit51

@[expose] public section

/-! Readd the root-bearing deleted members before estimating the width.

The initial coarse width and interval preparation are separate inputs.  Only
actual deleted avoiders remain outside the readded family, so their complete
actual ceil-fringe count replaces the old 485N deletion loss.  No lower-startup
global conclusion is asserted by this local prepared-family interface.
-/
namespace JSP233.RawEndpoint114
open StarCompletion APGeometry DenseDeletion40 LongTerminal35
open HarmonicAbel29 HarmonicLog55 RawEndpoint112
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

def Readded (N : ℕ) (F : Finset (Finset ℤ)) (c : ℤ) : Finset (Finset ℤ) :=
  F \ TerminalDeficit51.OmittedAvoiders N 11 F c

def CorePolynomial (x : ℝ) : ℝ :=
  x ^ 3 / 6 + 11 * x ^ 2 / 2 + (1961 / 125 : ℝ) * x + 2041349 / 62500

def RefinedPolynomial (x : ℝ) : ℝ := (114959 / 3359 : ℝ) * CorePolynomial x

theorem actual_retained_subset_readded (N : ℕ) (F : Finset (Finset ℤ)) (c : ℤ) :
    Retained N 11 F ⊆ Readded N F c := by
  intro S hS
  obtain ⟨hSF, hnot⟩ := Finset.mem_sdiff.mp hS
  apply Finset.mem_sdiff.mpr
  refine ⟨hSF, ?_⟩
  intro hE
  exact hnot (Finset.mem_filter.mp hE).1

/-- The readded root-bearing deleted members cause no new avoider. -/
theorem actual_readded_root {N : ℕ} {F : Finset (Finset ℤ)} {c : ℤ}
    (hroot : ∀ S ∈ Retained N 11 F, ¬ IsAP S → c ∈ S) :
    ∀ S ∈ Readded N F c, ¬ IsAP S → c ∈ S := by
  intro S hS hbad
  by_contra hcS
  have hv : S ∈ Avoiders (Readded N F c) c := Finset.mem_filter.mpr ⟨hS, hcS⟩
  have ha := TerminalDeficit51.actual_avoider_readdition N 11 F c
  change Avoiders (Readded N F c) c = _ at ha
  rw [ha] at hv
  exact hcS (hroot S (Finset.mem_filter.mp hv).1 hbad)

/-- The old complete prepared-family raw estimate now pays all of the
readded family.  Only actual deleted avoiders, not all deleted members, remain.
No cardinality estimate for those avoiders is assumed here. -/
theorem actual_readded11_raw_half {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (hc : (c : ℤ) ∈ Ground N) (hF : Legal (Ground N) F)
    (hcL : c < L) (hLR : L ≤ R) (hRN : R ≤ N)
    (hroot : ∀ S ∈ Retained N 11 F, ¬ IsAP S → (c : ℤ) ∈ S)
    (hP : P ∈ Retained N 11 F) (hcP : (c : ℤ) ∉ P) (hLP : ∀ z ∈ P, (L : ℤ) ≤ z)
    (hT : T ∈ Retained N 11 F) (hcT : (c : ℤ) ∉ T) (hTR : ∀ z ∈ T, z ≤ (R : ℤ))
    (houtside : ∀ S ∈ Retained N 11 F, (c : ℤ) ∉ S →
      (∃ u ∈ S, u ≤ (L : ℤ)) ∧ ∃ v ∈ S, (R : ℤ) ≤ v) :
    (F.card : ℝ) ≤ (N : ℝ) ^ 2 / 2 - DeficitCoeff * ((L : ℝ) + (N - R)) ^ 2 +
      N * SimplexPolynomial (Real.log N) (Harmonic N) / 2 + 4 * N * (Harmonic N) ^ 2 +
      6 * N * Harmonic N + 24 * N + (L - c : ℕ) + 3 +
      (TerminalDeficit51.OmittedAvoiders N 11 F (c : ℤ)).card := by
  let E := TerminalDeficit51.OmittedAvoiders N 11 F (c : ℤ)
  let G := Readded N F (c : ℤ)
  have hEF : E ⊆ F := (Finset.filter_subset _ _).trans (actual_deleted_subset N 11 F)
  have hGF : G ⊆ F := Finset.sdiff_subset
  have hGlegal : Legal (Ground N) G := ⟨fun S hS => hF.1 S (hGF hS),
    fun S hS U hU he => hF.2 S (hGF hS) U (hGF hU) he⟩
  have hsub := actual_retained_subset_readded N F (c : ℤ)
  have ha := TerminalDeficit51.actual_avoider_readdition N 11 F (c : ℤ)
  have hout : ∀ S ∈ G, (c : ℤ) ∉ S →
      (∃ u ∈ S, u ≤ (L : ℤ)) ∧ ∃ v ∈ S, (R : ℤ) ≤ v := by
    intro S hS hcS
    have hv : S ∈ Avoiders G (c : ℤ) := Finset.mem_filter.mpr ⟨hS, hcS⟩
    change Avoiders G (c : ℤ) = _ at ha
    rw [ha] at hv
    exact houtside S (Finset.mem_filter.mp hv).1 hcS
  have hr := RawEndpoint112.actual_prepared_family_raw_half hc hGlegal hcL hLR hRN
    (actual_readded_root hroot) (hsub hP) hcP hLP (hsub hT) hcT hTR hout
  have hcard := Finset.card_sdiff_add_card_eq_card hEF
  have hcardR : (G.card : ℝ) + E.card = F.card := by exact_mod_cast hcard
  dsimp only [E] at hcardR
  linarith only [hr, hcardR]

/-- The 55-price applies to the actual deleted avoiders of this same original
family.  The AP containing [L,R] is an actual interval omitter, not a phantom
core.  The strict large-width branch is retained. -/
theorem actual_deleted_avoider_count55 {N c L R : ℕ} {F : Finset (Finset ℤ)}
    (hN : 225 ≤ N) (hc : (c : ℤ) ∈ Ground N) (hF : Legal (Ground N) F)
    (hcL : c < L) (hLR : L ≤ R) (hRN : R ≤ N)
    (hne : (Avoiders (Retained N 11 F) (c : ℤ)).Nonempty)
    (hi : ∀ S ∈ Avoiders (Retained N 11 F) (c : ℤ), ∃ a b : ℕ,
      c < a ∧ a ≤ L ∧ R ≤ b ∧ b ≤ N ∧ S = Interval (a, b))
    (hthin : 42 * (L + N - R) ≤ N) (hlarge : 90 < L + N - R) :
    (TerminalDeficit51.OmittedAvoiders N 11 F (c : ℤ)).card ≤ 55 * (L + N - R) := by
  let E := TerminalDeficit51.OmittedAvoiders N 11 F (c : ℤ)
  have hEF : E ⊆ F := (Finset.filter_subset _ _).trans (actual_deleted_subset N 11 F)
  have hbad : ∀ S ∈ E, ¬ IsAP S := by
    intro S hS
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).2.1
  have hdense : ∀ S ∈ E, N < 11 * S.card := by
    intro S hS
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).2.2
  obtain ⟨H, hHG, hHAP, hKH⟩ := RestoreTerminal35.actual_interval_core_member
    N c L R (Retained N 11 F) hLR hne hi
  have hHF : H ∈ F := (Finset.mem_sdiff.mp hHG).1
  have hcN := (mem_ground N (c : ℤ)).mp hc
  have hL : 1 ≤ L := by omega
  have hgeo : 165 * (L + N - R) ≤ 4 * N := by omega
  have hb := CeilFringe113.actual_dense_fringe_bound55 hN hL hLR hRN hlarge
    hF hEF hbad hdense ⟨H, hHF, hHAP, hKH⟩ hgeo
  have hext := ThinFringe33.ground_interval_exterior_card N (by exact_mod_cast hL : (1 : ℤ) ≤ L)
    (by exact_mod_cast hLR : (L : ℤ) ≤ R) (by exact_mod_cast hRN : (R : ℤ) ≤ N)
  have hextle : (Ground N \ Finset.Icc (L : ℤ) (R : ℤ)).card ≤ L + N - R := by omega
  exact hb.trans (Nat.mul_le_mul_left 55 hextle)

theorem core_harmonic_identity (x : ℝ) :
    SimplexPolynomial x (x + 293 / 500) / 2 + 4 * (x + 293 / 500) ^ 2 +
      6 * (x + 293 / 500) + 128 / 5 = CorePolynomial x := by
  dsimp only [SimplexPolynomial, CorePolynomial]
  ring

/-- Actual readded-family width, after a separately established coarse width
and actual interval preparation.  It is not a standalone original-family
upper bound and cannot be used to justify its own thinness premise. -/
theorem actual_readded11_width {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (hN : 3000 ≤ N) (hc : (c : ℤ) ∈ Ground N) (hF : Legal (Ground N) F)
    (hcard : B N ≤ F.card) (hcL : c < L) (hLR : L ≤ R) (hRN : R ≤ N)
    (hroot : ∀ S ∈ Retained N 11 F, ¬ IsAP S → (c : ℤ) ∈ S)
    (hP : P ∈ Retained N 11 F) (hcP : (c : ℤ) ∉ P) (hLP : ∀ z ∈ P, (L : ℤ) ≤ z)
    (hT : T ∈ Retained N 11 F) (hcT : (c : ℤ) ∉ T) (hTR : ∀ z ∈ T, z ≤ (R : ℤ))
    (houtside : ∀ S ∈ Retained N 11 F, (c : ℤ) ∉ S →
      (∃ u ∈ S, u ≤ (L : ℤ)) ∧ ∃ v ∈ S, (R : ℤ) ≤ v)
    (hi : ∀ S ∈ Avoiders (Retained N 11 F) (c : ℤ), ∃ a b : ℕ,
      c < a ∧ a ≤ L ∧ R ≤ b ∧ b ≤ N ∧ S = Interval (a, b))
    (hthin : 42 * (L + N - R) ≤ N) (hlarge : 90 < L + N - R) :
    ((L : ℝ) + (N - R)) ^ 2 ≤ (N : ℝ) * RefinedPolynomial (Real.log N) := by
  have hr := actual_readded11_raw_half hc hF hcL hLR hRN hroot
    hP hcP hLP hT hcT hTR houtside
  have hne : (Avoiders (Retained N 11 F) (c : ℤ)).Nonempty :=
    ⟨P, Finset.mem_filter.mpr ⟨hP, hcP⟩⟩
  have hcount := actual_deleted_avoider_count55 (by omega : 225 ≤ N)
    hc hF hcL hLR hRN hne hi hthin hlarge
  have hcountR : ((TerminalDeficit51.OmittedAvoiders N 11 F (c : ℤ)).card : ℝ) ≤
      55 * ((L + N - R : ℕ) : ℝ) := by exact_mod_cast hcount
  have hb := RawEndpoint113.original_quarter_card_lower (by omega : 1 ≤ N) hcard
  have hn : (3000 : ℝ) ≤ N := by exact_mod_cast hN
  have he : ((L + N - R : ℕ) : ℝ) = (L : ℝ) + (N - R) := by
    rw [Nat.cast_sub (by omega : R ≤ L + N), Nat.cast_add]
    ring
  rw [he] at hcountR
  have ht : (42 : ℝ) * ((L : ℝ) + (N - R)) ≤ N := by
    have hh : (42 : ℝ) * ((L + N - R : ℕ) : ℝ) ≤ N := by exact_mod_cast hthin
    rwa [he] at hh
  have hd : ((L - c : ℕ) : ℝ) ≤ (L : ℝ) + (N - R) := by
    have hh : ((L - c : ℕ) : ℝ) ≤ ((L + N - R : ℕ) : ℝ) := by
      exact_mod_cast (by omega : L - c ≤ L + N - R)
    rwa [he] at hh
  have hcost : DeficitCoeff * ((L : ℝ) + (N - R)) ^ 2 ≤
      (N : ℝ) * (SimplexPolynomial (Real.log N) (Harmonic N) / 2 +
        4 * (Harmonic N) ^ 2 + 6 * Harmonic N + 128 / 5) := by
    nlinarith only [hr, hb, hcountR, ht, hd, hn]
  have hh := actual_harmonic_log_586 (N := N) (by omega : 63 ≤ N)
  have hh0 := harmonic_nonneg N
  have hl0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by linarith only [hn])
  have hhsq : (Harmonic N) ^ 2 ≤ (Real.log (N : ℝ) + 293 / 500) ^ 2 := by gcongr
  have hp : SimplexPolynomial (Real.log N) (Harmonic N) / 2 +
      4 * (Harmonic N) ^ 2 + 6 * Harmonic N + 128 / 5 ≤ CorePolynomial (Real.log N) := by
    rw [← core_harmonic_identity]
    dsimp only [SimplexPolynomial]
    nlinarith only [hh, hhsq]
  have htotal := hcost.trans (mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg N))
  dsimp only [DeficitCoeff] at htotal
  dsimp only [RefinedPolynomial]
  nlinarith only [htotal]

#print axioms actual_retained_subset_readded
#print axioms actual_readded_root
#print axioms actual_readded11_raw_half
#print axioms actual_deleted_avoider_count55
#print axioms core_harmonic_identity
#print axioms actual_readded11_width
end
end JSP233.RawEndpoint114
