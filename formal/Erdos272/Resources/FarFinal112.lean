import Erdos272.Resources.FarJoint112
import Erdos272.Core.FarShort112

/-! Complete actual Far bound, including Short maximum cores and all shell
directions.  Long and Short use one physical pool; the Short intrinsic exclusion
is already part of FarJoint112.  Near members are not paid by this module.
-/
namespace JSP233.FarFinal112
open StarCompletion APGeometry NearAP36 FarSlot112 FarCapacity112 FarJoint112 FarShort112
open scoped Classical BigOperators
noncomputable section

theorem short_codes_subset_intrinsic {N D : ℕ} {S : Finset ℤ}
    (hS : S ⊆ Ground N) : ShortCodes S D ⊆ IntrinsicSlotCodes N D S := by
  intro q hq
  exact mem_intrinsicSlotCodes.mpr (actual_short_codes hS hq)

/-- No maximum core, step, intrinsic mass, or capacity is assumed here.
All are constructed from the same complete actual non-Near source family. -/
theorem actual_far_joint_bound {N K : ℕ} {F : Finset (Finset ℤ)}
    (hF : Legal (Ground N) F) (hK : 0 < K)
    (hsize : ∀ S ∈ F, 3 * K ≤ S.card)
    (hfar : ∀ S ∈ F, ¬ HasNearAPCore K S) :
    let t := 5 * K / 3
    K * t * F.card ≤ 2 * ((N - 1) / t) * N ^ 2 := by
  let t := 5 * K / 3
  let M := t + 1
  let D := (N - 1) / t
  obtain ⟨ht, hM, hsq⟩ := far_cutoff_arithmetic hK
  change 1 ≤ t at ht
  change M ≤ 3 * K at hM
  change K * t ≤ (3 * K - t) ^ 2 at hsq
  have hM2 : 2 ≤ M := by dsimp [M]; omega
  have hMsub : M - 1 = t := rfl
  obtain ⟨core, step, hcoords⟩ := exists_maximum_core_selection
    (F := F) (fun S hS => Finset.card_pos.mp (by have := hsize S hS; omega))
  let short : Finset ℤ → Prop := fun S => (core S).card < M
  have hmax : ∀ S ∈ F, MaximalAPCore S (core S) :=
    fun S hS => maximum_core_is_maximal (hcoords S hS).1
  have hAt : ∀ S ∈ F, ∃ p, APAt (step S) p (core S) := fun S hS => (hcoords S hS).2
  have hcut : ∀ S ∈ F, ¬ short S → 1 ≤ step S ∧ step S ≤ D := by
    intro S hS hLong
    obtain ⟨p, hP⟩ := hAt S hS
    have hh := actual_core_step_bound hP (isAP_nonempty (hcoords S hS).1.2.1)
      ((hcoords S hS).1.1.trans (hF.1 S hS)) hM2 (by dsimp [short] at hLong; omega)
    simpa only [hMsub] using hh
  have hmass : ∀ S ∈ F, K * t ≤ (JointCodes N D core step short S).card := by
    intro S hS
    by_cases hs : short S
    · simp only [JointCodes, if_pos hs]
      have hSc : M ≤ S.card := hM.trans (hsize S hS)
      have hsmall := actual_short_source_mass (hF.1 S hS) (hcoords S hS).1 hM2 hSc hs
      have hsub := short_codes_subset_intrinsic (D := D) (hF.1 S hS)
      have hbase : 3 * K - t ≤ S.card - M + 1 := by
        dsimp [M]
        have := hsize S hS
        omega
      have hpow := Nat.pow_le_pow_left hbase 2
      have hshort : (S.card - M + 1) ^ 2 ≤ (IntrinsicSlotCodes N D S).card := by
        have hh := hsmall.trans (Finset.card_le_card hsub)
        simpa only [hMsub] using hh
      exact hsq.trans (hpow.trans hshort)
    · simp only [JointCodes, if_neg hs]
      obtain ⟨p, hP⟩ := hAt S hS
      rw [coreShellCodes_card hP (isAP_nonempty (hcoords S hS).1.2.1)]
      have hPc : t ≤ (core S).card - 1 := by dsimp [short, M] at hs; omega
      have he : K ≤ (S \ core S).card :=
        non_near_core_shell_mass (hmax S hS) (hsize S hS) (hfar S hS)
      nlinarith [Nat.mul_le_mul hPc he]
  exact actual_joint_count_of_mass hF core step short hmax hAt hcut hmass

/-- The complete cubic Far estimate with the exact integer cutoff t. -/
theorem actual_far_cubic_nat {N K : ℕ} {F : Finset (Finset ℤ)}
    (hF : Legal (Ground N) F) (hK : 0 < K)
    (hsize : ∀ S ∈ F, 3 * K ≤ S.card)
    (hfar : ∀ S ∈ F, ¬ HasNearAPCore K S) :
    K * (5 * K / 3) ^ 2 * F.card ≤ 2 * N ^ 3 := by
  let t := 5 * K / 3
  let D := (N - 1) / t
  have hj := actual_far_joint_bound hF hK hsize hfar
  change K * t * F.card ≤ 2 * D * N ^ 2 at hj
  have hDt : D * t ≤ N := (Nat.div_mul_le_self (N - 1) t).trans (Nat.sub_le N 1)
  calc
    K * t ^ 2 * F.card = (K * t * F.card) * t := by ring
    _ ≤ (2 * D * N ^ 2) * t := Nat.mul_le_mul_right t hj
    _ = (2 * N ^ 2) * (D * t) := by ring
    _ ≤ (2 * N ^ 2) * N := Nat.mul_le_mul_left _ hDt
    _ = 2 * N ^ 3 := by ring

theorem actual_far_cubic_real {N K : ℕ} {F : Finset (Finset ℤ)}
    (hF : Legal (Ground N) F) (hK : 0 < K)
    (hsize : ∀ S ∈ F, 3 * K ≤ S.card)
    (hfar : ∀ S ∈ F, ¬ HasNearAPCore K S) :
    (F.card : ℝ) ≤ 2 * (N : ℝ) ^ 3 / ((K : ℝ) * ((5 * K / 3 : ℕ) : ℝ) ^ 2) := by
  have hh := actual_far_cubic_nat hF hK hsize hfar
  have hreal : (K : ℝ) * ((5 * K / 3 : ℕ) : ℝ) ^ 2 * (F.card : ℝ) ≤ 2 * (N : ℝ) ^ 3 := by
    exact_mod_cast hh
  have ht : 0 < (5 * K / 3 : ℕ) := by have := (far_cutoff_arithmetic hK).1; omega
  have hd : 0 < (K : ℝ) * ((5 * K / 3 : ℕ) : ℝ) ^ 2 := by positivity
  exact (le_div_iff₀ hd).mpr (by nlinarith)

theorem actual_far_normalized {N K : ℕ} {F : Finset (Finset ℤ)}
    (hF : Legal (Ground N) F) (hK : 0 < K) (hN : 0 < N)
    (hsize : ∀ S ∈ F, 3 * K ≤ S.card)
    (hfar : ∀ S ∈ F, ¬ HasNearAPCore K S) :
    (F.card : ℝ) / (N : ℝ) ^ 2 ≤
      2 * (N : ℝ) / ((K : ℝ) * ((5 * K / 3 : ℕ) : ℝ) ^ 2) := by
  have hb := actual_far_cubic_real hF hK hsize hfar
  have hN2 : 0 < (N : ℝ) ^ 2 := by positivity
  apply (div_le_iff₀ hN2).mpr
  have he : 2 * (N : ℝ) / ((K : ℝ) * ((5 * K / 3 : ℕ) : ℝ) ^ 2) * (N : ℝ) ^ 2 =
      2 * (N : ℝ) ^ 3 / ((K : ℝ) * ((5 * K / 3 : ℕ) : ℝ) ^ 2) := by ring
  rw [he]
  exact hb

/-- Direct application to the complete fixed-scale Far filter of any original
Legal family.  AP sources are retained in the original family and receive
their own Near accounting; none are silently removed from the original F. -/
theorem actual_fixed_far_filter_bound {N K : ℕ} {F : Finset (Finset ℤ)}
    (hF : Legal (Ground N) F) (hK : 0 < K) :
    let H := F.filter (fun S => 3 * K ≤ S.card ∧ ¬ HasNearAPCore K S)
    K * (5 * K / 3) ^ 2 * H.card ≤ 2 * N ^ 3 := by
  dsimp
  let H := F.filter (fun S => 3 * K ≤ S.card ∧ ¬ HasNearAPCore K S)
  have hsub : H ⊆ F := Finset.filter_subset _ _
  have hlegal : Legal (Ground N) H := ⟨fun S hS => hF.1 S (hsub hS),
    fun S hS T hT hne => hF.2 S (hsub hS) T (hsub hT) hne⟩
  exact actual_far_cubic_nat hlegal hK
    (fun S hS => (Finset.mem_filter.mp hS).2.1)
    (fun S hS => (Finset.mem_filter.mp hS).2.2)

#print axioms short_codes_subset_intrinsic
#print axioms actual_far_joint_bound
#print axioms actual_far_cubic_nat
#print axioms actual_far_cubic_real
#print axioms actual_far_normalized
#print axioms actual_fixed_far_filter_bound

end
end JSP233.FarFinal112
