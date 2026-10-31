import Erdos272.Core.FarSlot112
import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-! Double counting actual maximal-core/physical-shell slots.

This module uses the proved actual capacity from FarSlot112.  It never assumes
an abstract slot bound.  The Long interface retains each core edge and every
physical shell point.  The complete Long/Short Far assembly is a separate step.
-/
namespace JSP233.FarCapacity112
open StarCompletion APGeometry NearAP36 FarSlot112
open scoped Classical BigOperators
noncomputable section

/-- Maximum cardinality among all actual AP subsets of the source.  This is
stronger than inclusion maximality and is needed for the Short classification. -/
def MaximumAPCore (S P : Finset ℤ) : Prop :=
  P ⊆ S ∧ IsAP P ∧ ∀ U : Finset ℤ, U ⊆ S → IsAP U → U.card ≤ P.card

theorem exists_maximum_AP_core {S : Finset ℤ} (hS : S.Nonempty) :
    ∃ P, MaximumAPCore S P := by
  obtain ⟨a, ha⟩ := hS
  let A := S.powerset.filter IsAP
  have hA : ({a} : Finset ℤ) ∈ A := Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr (by simpa using ha), singleton_isAP a⟩
  obtain ⟨P, hP, hmax⟩ := Finset.exists_max_image A Finset.card ⟨{a}, hA⟩
  obtain ⟨hPS, hAP⟩ := Finset.mem_filter.mp hP
  refine ⟨P, Finset.mem_powerset.mp hPS, hAP, ?_⟩
  intro U hUS hUAP
  exact hmax U (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hUS, hUAP⟩)

theorem maximum_core_is_maximal {S P : Finset ℤ} (hP : MaximumAPCore S P) :
    MaximalAPCore S P := by
  refine ⟨hP.1, hP.2.1, ?_⟩
  intro U hPU hUS hUAP
  exact (Finset.eq_of_subset_of_card_le hPU (hP.2.2 U hUS hUAP)).symm

theorem maximum_core_card_ge_two {S P : Finset ℤ}
    (hP : MaximumAPCore S P) (hS : 2 ≤ S.card) : 2 ≤ P.card := by
  obtain ⟨a, b, ha, hb, hne⟩ := Finset.one_lt_card_iff.mp (by omega : 1 < S.card)
  have hh := hP.2.2 {a, b} (by intro x hx; simp only [Finset.mem_insert,
    Finset.mem_singleton] at hx; rcases hx with rfl | rfl <;> assumption) (pair_isAP a b)
  simpa only [Finset.card_pair hne] using hh

/-- The actual non-Near predicate supplies the complete shell mass at size 3K. -/
theorem non_near_core_shell_mass {K : ℕ} {S P : Finset ℤ}
    (hP : MaximalAPCore S P) (hlarge : 3 * K ≤ S.card)
    (hnot : ¬ HasNearAPCore K S) : K ≤ (S \ P).card := by
  by_contra hsmall
  have hs := Finset.card_sdiff_add_card_eq_card hP.1
  have hPc : 2 * K + 1 ≤ P.card := by omega
  exact hnot ⟨P, hP, hPc, by omega⟩

def CoreEdges (P : Finset ℤ) (d : ℤ) : Finset ℤ :=
  P.filter (fun a => a + d ∈ P)

theorem coreEdges_eq_erase_max {P : Finset ℤ} {d p : ℤ}
    (hP : APAt d p P) (hne : P.Nonempty) :
    CoreEdges P d = P.erase (P.max' hne) := by
  have hd : 0 < d := hP.1
  have hmax : P.max' hne ∈ P := Finset.max'_mem P hne
  ext a
  simp only [CoreEdges, Finset.mem_filter, Finset.mem_erase]
  constructor
  · rintro ⟨ha, hb⟩
    refine ⟨?_, ha⟩
    have hbmax := Finset.le_max' P (a + d) hb
    omega
  · rintro ⟨hamax, ha⟩
    refine ⟨ha, ?_⟩
    have ham : a < P.max' hne := lt_of_le_of_ne (Finset.le_max' P a ha) hamax
    have hdiv : d ∣ P.max' hne - a := apAt_dvd_sub hP ha hmax
    have hle : d ≤ P.max' hne - a := Int.le_of_dvd (by omega) hdiv
    apply apAt_fill hP ha hmax (by omega) (by omega)
    simpa only [add_sub_cancel_left] using dvd_refl d

theorem coreEdges_card {P : Finset ℤ} {d p : ℤ}
    (hP : APAt d p P) (hne : P.Nonempty) :
    (CoreEdges P d).card = P.card - 1 := by
  rw [coreEdges_eq_erase_max hP hne, Finset.card_erase_of_mem (Finset.max'_mem P hne)]

def CoreShellCodes (S P : Finset ℤ) (d : ℕ) : Finset (ℕ × (ℤ × ℤ)) :=
  ((CoreEdges P d) ×ˢ (S \ P)).image (fun q => (d, q))

theorem mem_coreShellCodes {S P : Finset ℤ} {d : ℕ} {q : ℕ × (ℤ × ℤ)} :
    q ∈ CoreShellCodes S P d ↔ q.1 = d ∧ q.2.1 ∈ P ∧
      q.2.1 + (d : ℤ) ∈ P ∧ q.2.2 ∈ S \ P := by
  rcases q with ⟨e, a, x⟩
  simp only [CoreShellCodes, Finset.mem_image, Finset.mem_product, CoreEdges,
    Finset.mem_filter, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨b, y⟩, ⟨⟨hb, hbd⟩, hy⟩, he, hbx⟩
    obtain rfl := he
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hbx
    exact ⟨rfl, hb, hbd, hy⟩
  · rintro ⟨rfl, ha, had, hx⟩
    exact ⟨(a, x), ⟨⟨ha, had⟩, hx⟩, rfl, rfl⟩

theorem coreShellCodes_card {S P : Finset ℤ} {d : ℕ} {p : ℤ}
    (hP : APAt d p P) (hne : P.Nonempty) :
    (CoreShellCodes S P d).card = (P.card - 1) * (S \ P).card := by
  have hinj : Function.Injective (fun q : ℤ × ℤ => (d, q)) := by
    intro u v h
    exact (Prod.mk.inj h).2
  rw [CoreShellCodes, Finset.card_image_of_injective _ hinj, Finset.card_product,
    coreEdges_card hP hne]

def PhysicalSlots (N D : ℕ) : Finset (ℕ × (ℤ × ℤ)) :=
  Finset.Icc 1 D ×ˢ (Ground N ×ˢ Ground N)

theorem physicalSlots_card (N D : ℕ) :
    (PhysicalSlots N D).card = D * N ^ 2 := by
  simp only [PhysicalSlots, Finset.card_product, ground_card, Nat.card_Icc]
  have he : D + 1 - 1 = D := by omega
  rw [he, pow_two]

theorem coreShellCodes_subset_slots {N D d : ℕ} {S P : Finset ℤ}
    (hS : S ⊆ Ground N) (hP : P ⊆ S) (hd : 1 ≤ d) (hdD : d ≤ D) :
    CoreShellCodes S P d ⊆ PhysicalSlots N D := by
  intro q hq
  obtain ⟨he, ha, _, hx⟩ := mem_coreShellCodes.mp hq
  apply Finset.mem_product.mpr
  refine ⟨Finset.mem_Icc.mpr (he ▸ ⟨hd, hdD⟩), ?_⟩
  exact Finset.mem_product.mpr ⟨hS (hP ha), hS (Finset.mem_sdiff.mp hx).1⟩

/-- All sources using one fixed physical slot satisfy its actual capacity.
The selected step is allowed to vary over the original source family. -/
theorem actual_code_fiber_card_le_two {Ω : Finset ℤ} {F : Finset (Finset ℤ)}
    (hF : Legal Ω F) (core : Finset ℤ → Finset ℤ) (step : Finset ℤ → ℕ)
    (hcore : ∀ S ∈ F, MaximalAPCore S (core S))
    (hAt : ∀ S ∈ F, ∃ p, APAt (step S) p (core S)) (q : ℕ × (ℤ × ℤ)) :
    (F.filter (fun S => q ∈ CoreShellCodes S (core S) (step S))).card ≤ 2 := by
  let H := F.filter (fun S => q ∈ CoreShellCodes S (core S) (step S))
  have hsub : H ⊆ F := Finset.filter_subset _ _
  have hlegal : Legal Ω H := ⟨fun S hS => hF.1 S (hsub hS),
    fun S hS T hT hne => hF.2 S (hsub hS) T (hsub hT) hne⟩
  have hdata : ∀ S ∈ H, q.1 = step S ∧ q.2.1 ∈ core S ∧
      q.2.1 + (q.1 : ℤ) ∈ core S ∧ q.2.2 ∈ S \ core S := by
    intro S hS
    have hh := mem_coreShellCodes.mp (Finset.mem_filter.mp hS).2
    exact ⟨hh.1, hh.2.1, hh.1 ▸ hh.2.2.1, hh.2.2.2⟩
  exact actual_slot_card_le_two hlegal core (fun S hS => hcore S (hsub hS))
    (by
      intro S hS
      obtain ⟨p, hP⟩ := hAt S (hsub hS)
      have hrep := apAt_rebase hP (hdata S hS).2.1
      simpa only [← (hdata S hS).1] using hrep)
    (fun S hS => (hdata S hS).2.1) (fun S hS => (hdata S hS).2.2.1)
    (fun S hS => (hdata S hS).2.2.2)

/-- Complete actual Long-source count.  Every adjacent core edge and every
shell point is charged to the same physical slot pool, with multiplicity two
proved from actual Legal intersections rather than supplied as a hypothesis. -/
theorem actual_long_core_bound {N D K M : ℕ} {F : Finset (Finset ℤ)}
    (hF : Legal (Ground N) F) (core : Finset ℤ → Finset ℤ)
    (step : Finset ℤ → ℕ)
    (hcore : ∀ S ∈ F, MaximalAPCore S (core S))
    (hAt : ∀ S ∈ F, ∃ p, APAt (step S) p (core S))
    (hstep : ∀ S ∈ F, 1 ≤ step S ∧ step S ≤ D)
    (hmass : ∀ S ∈ F, M ≤ (core S).card ∧ K ≤ (S \ core S).card) :
    K * (M - 1) * F.card ≤ 2 * D * N ^ 2 := by
  let slots := PhysicalSlots N D
  let rel : Finset ℤ → (ℕ × (ℤ × ℤ)) → Prop :=
    fun S q => q ∈ CoreShellCodes S (core S) (step S)
  have hcodes : ∀ S ∈ F, CoreShellCodes S (core S) (step S) ⊆ slots := by
    intro S hS
    exact coreShellCodes_subset_slots (hF.1 S hS) (hcore S hS).1
      (hstep S hS).1 (hstep S hS).2
  have hcount := Finset.card_mul_le_card_mul (s := F) (t := slots) (r := rel)
    (m := K * (M - 1)) (n := 2)
    (by
      intro S hS
      have he : slots.bipartiteAbove rel S = CoreShellCodes S (core S) (step S) := by
        ext q
        simp only [Finset.mem_bipartiteAbove]
        exact and_iff_right_of_imp (fun hq => hcodes S hS hq)
      rw [he]
      obtain ⟨p, hP⟩ := hAt S hS
      rw [coreShellCodes_card hP (isAP_nonempty (hcore S hS).2.1)]
      have hm := Nat.sub_le_sub_right (hmass S hS).1 1
      nlinarith [Nat.mul_le_mul hm (hmass S hS).2])
    (by
      intro q _
      exact actual_code_fiber_card_le_two hF core step hcore hAt q)
  dsimp [slots] at hcount
  rw [physicalSlots_card] at hcount
  nlinarith

/-- The ambient span supplies the step cutoff for every actual Long core. -/
theorem actual_core_step_bound {N M d : ℕ} {P : Finset ℤ} {p : ℤ}
    (hP : APAt d p P) (hne : P.Nonempty) (hground : P ⊆ Ground N)
    (hM : 2 ≤ M) (hcard : M ≤ P.card) :
    1 ≤ d ∧ d ≤ (N - 1) / (M - 1) := by
  have hd : 0 < d := by exact_mod_cast hP.1
  have hspan := apAt_card_span hP hne
    (fun x hx => Finset.mem_Icc.mpr ((mem_ground N x).mp (hground hx)))
  obtain ⟨a, ha⟩ := hne
  have hN : 1 ≤ N := by have := (mem_ground N a).mp (hground ha); omega
  have hc : 1 ≤ P.card := by omega
  have hs : d * (P.card - 1) ≤ N - 1 := by
    have hh : ((d * (P.card - 1) : ℕ) : ℤ) ≤ ((N - 1 : ℕ) : ℤ) := by
      simpa only [Nat.cast_mul, Nat.cast_sub hc, Nat.cast_sub hN, Nat.cast_one] using hspan
    exact_mod_cast hh
  refine ⟨by omega, (Nat.le_div_iff_mul_le (by omega : 0 < M - 1)).mpr ?_⟩
  exact (Nat.mul_le_mul_left d (Nat.sub_le_sub_right hcard 1)).trans hs

/-- Actual non-Near Long sources: neither their shell mass nor step cutoff is
an extra counting premise.  Both are derived from the original objects. -/
theorem actual_non_near_long_bound {N K M : ℕ} {F : Finset (Finset ℤ)}
    (hF : Legal (Ground N) F) (core : Finset ℤ → Finset ℤ)
    (step : Finset ℤ → ℕ)
    (hcore : ∀ S ∈ F, MaximumAPCore S (core S))
    (hAt : ∀ S ∈ F, ∃ p, APAt (step S) p (core S)) (hM : 2 ≤ M)
    (hlarge : ∀ S ∈ F, 3 * K ≤ S.card)
    (hnot : ∀ S ∈ F, ¬ HasNearAPCore K S)
    (hLong : ∀ S ∈ F, M ≤ (core S).card) :
    K * (M - 1) * F.card ≤ 2 * ((N - 1) / (M - 1)) * N ^ 2 := by
  have hmax : ∀ S ∈ F, MaximalAPCore S (core S) :=
    fun S hS => maximum_core_is_maximal (hcore S hS)
  apply actual_long_core_bound hF core step hmax hAt
  · intro S hS
    obtain ⟨p, hP⟩ := hAt S hS
    exact actual_core_step_bound hP (isAP_nonempty (hcore S hS).2.1)
      ((hcore S hS).1.trans (hF.1 S hS)) hM (hLong S hS)
  · intro S hS
    exact ⟨hLong S hS, non_near_core_shell_mass (hmax S hS) (hlarge S hS) (hnot S hS)⟩

#print axioms coreEdges_eq_erase_max
#print axioms exists_maximum_AP_core
#print axioms maximum_core_is_maximal
#print axioms maximum_core_card_ge_two
#print axioms non_near_core_shell_mass
#print axioms coreEdges_card
#print axioms mem_coreShellCodes
#print axioms coreShellCodes_card
#print axioms physicalSlots_card
#print axioms coreShellCodes_subset_slots
#print axioms actual_code_fiber_card_le_two
#print axioms actual_long_core_bound
#print axioms actual_core_step_bound
#print axioms actual_non_near_long_bound

end
end JSP233.FarCapacity112
