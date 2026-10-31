import Erdos272.Resources.FarFinal112

/-! Stronger complete actual Far payment.

The Long branch keeps the relation between core size and shell size, rather
than replacing both by independent lower bounds.  It is combined with the
already proved actual Short codes in the same physical pool.  No new capacity,
source selection, root, or omitted-member hypothesis is assumed.
-/
namespace JSP233.FarJoint113
open StarCompletion APGeometry NearAP36 FarSlot112 FarCapacity112 FarJoint112
  FarShort112 FarFinal112
open scoped Classical BigOperators
noncomputable section

def Mass (K : ℕ) : ℕ := K * (2 * K - 1)
def Cutoff (K : ℕ) : ℕ := 19 * K / 12

/-- Core edges and shell size cannot simultaneously attain the two separate
lower bounds used in the old count. -/
theorem long_mass_arithmetic {K m e : ℕ} (hK : 0 < K)
    (hm : K + 1 ≤ m) (he : K ≤ e) (hsize : 3 * K ≤ m + e) :
    Mass K ≤ (m - 1) * e := by
  have hm1 : 1 ≤ m := by omega
  have hK2 : 1 ≤ 2 * K := by omega
  have hu : K ≤ m - 1 := by omega
  by_cases hhigh : 2 * K - 1 ≤ m - 1
  · calc
      Mass K = K * (2 * K - 1) := rfl
      _ ≤ e * (m - 1) := Nat.mul_le_mul he hhigh
      _ = (m - 1) * e := by ring
  · have hmid : m - 1 ≤ 2 * K - 1 := by omega
    have hprod := Nat.zero_le ((m - 1 - K) * (2 * K - 1 - (m - 1)))
    have hsub1 : m - 1 - K + K = m - 1 := Nat.sub_add_cancel hu
    have hsub2 : 2 * K - 1 - (m - 1) + (m - 1) = 2 * K - 1 :=
      Nat.sub_add_cancel hmid
    dsimp [Mass]
    zify [hm1, hK2, hu, hmid] at *
    nlinarith

/-- The rational cutoff is within 0.16 percent of the best continuous cutoff
for the stronger mass.  Its floor scales in the required direction. -/
theorem cutoff_arithmetic {K : ℕ} (hK : 0 < K) :
    K ≤ Cutoff K ∧ 1 ≤ Cutoff K ∧ Cutoff K + 1 ≤ 3 * K ∧
      Mass K ≤ (3 * K - Cutoff K) ^ 2 := by
  let t := Cutoff K
  have htK : K ≤ t := by dsimp [t, Cutoff]; omega
  have ht : 1 ≤ t := by omega
  have ht19 : 12 * t ≤ 19 * K := by
    dsimp [t, Cutoff]
    have hh := Nat.div_mul_le_self (19 * K) 12
    nlinarith
  have hM : t + 1 ≤ 3 * K := by omega
  let u := 3 * K - t
  have hu : 17 * K ≤ 12 * u := by dsimp [u]; omega
  have hsq := Nat.mul_le_mul hu hu
  have hK2 : 1 ≤ 2 * K := by omega
  refine ⟨htK, ht, hM, ?_⟩
  change Mass K ≤ u ^ 2
  calc
    Mass K = K * (2 * K - 1) := rfl
    _ ≤ K * (2 * K) := Nat.mul_le_mul_left K (Nat.sub_le (2 * K) 1)
    _ = 2 * K ^ 2 := by ring
    _ ≤ u ^ 2 := by nlinarith

theorem mass_pos {K : ℕ} (hK : 0 < K) : 0 < Mass K := by
  unfold Mass
  exact Nat.mul_pos hK (by omega)

/-- Complete actual Long/Short Far family, in one physical pool.  All maximum
cores and natural steps are constructed from the actual sources. -/
theorem actual_far_joint_bound {N K : ℕ} {F : Finset (Finset ℤ)}
    (hF : Legal (Ground N) F) (hK : 0 < K)
    (hsize : ∀ S ∈ F, 3 * K ≤ S.card)
    (hfar : ∀ S ∈ F, ¬ HasNearAPCore K S) :
    Mass K * F.card ≤ 2 * ((N - 1) / Cutoff K) * N ^ 2 := by
  let t := Cutoff K
  let M := t + 1
  let D := (N - 1) / t
  obtain ⟨htK, ht, hM, hsq⟩ := cutoff_arithmetic hK
  change K ≤ t at htK
  change 1 ≤ t at ht
  change M ≤ 3 * K at hM
  change Mass K ≤ (3 * K - t) ^ 2 at hsq
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
  have hmass : ∀ S ∈ F, Mass K ≤ (JointCodes N D core step short S).card := by
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
      apply long_mass_arithmetic hK
      · dsimp [short, M] at hs
        omega
      · exact non_near_core_shell_mass (hmax S hS) (hsize S hS) (hfar S hS)
      · have heq := Finset.card_sdiff_add_card_eq_card (hcoords S hS).1.1
        have hh := hsize S hS
        omega
  exact actual_joint_count_of_mass hF core step short hmax hAt hcut hmass

theorem actual_far_cubic_nat {N K : ℕ} {F : Finset (Finset ℤ)}
    (hF : Legal (Ground N) F) (hK : 0 < K)
    (hsize : ∀ S ∈ F, 3 * K ≤ S.card)
    (hfar : ∀ S ∈ F, ¬ HasNearAPCore K S) :
    Mass K * Cutoff K * F.card ≤ 2 * N ^ 3 := by
  have hj := actual_far_joint_bound hF hK hsize hfar
  have hDt : ((N - 1) / Cutoff K) * Cutoff K ≤ N :=
    (Nat.div_mul_le_self (N - 1) (Cutoff K)).trans (Nat.sub_le N 1)
  calc
    Mass K * Cutoff K * F.card = (Mass K * F.card) * Cutoff K := by ring
    _ ≤ (2 * ((N - 1) / Cutoff K) * N ^ 2) * Cutoff K :=
      Nat.mul_le_mul_right _ hj
    _ = (2 * N ^ 2) * (((N - 1) / Cutoff K) * Cutoff K) := by ring
    _ ≤ (2 * N ^ 2) * N := Nat.mul_le_mul_left _ hDt
    _ = 2 * N ^ 3 := by ring

theorem actual_far_normalized {N K : ℕ} {F : Finset (Finset ℤ)}
    (hF : Legal (Ground N) F) (hK : 0 < K) (hN : 0 < N)
    (hsize : ∀ S ∈ F, 3 * K ≤ S.card)
    (hfar : ∀ S ∈ F, ¬ HasNearAPCore K S) :
    (F.card : ℝ) / (N : ℝ) ^ 2 ≤
      2 * (N : ℝ) / ((Mass K : ℝ) * Cutoff K) := by
  have hh := actual_far_cubic_nat hF hK hsize hfar
  have hr : (Mass K : ℝ) * Cutoff K * (F.card : ℝ) ≤ 2 * (N : ℝ) ^ 3 := by
    exact_mod_cast hh
  have hm : 0 < (Mass K : ℝ) := by exact_mod_cast mass_pos hK
  have htN : 0 < Cutoff K := by have := (cutoff_arithmetic hK).2.1; omega
  have ht : 0 < (Cutoff K : ℝ) := by exact_mod_cast htN
  have hc : (F.card : ℝ) ≤ 2 * (N : ℝ) ^ 3 / ((Mass K : ℝ) * Cutoff K) :=
    (le_div_iff₀ (mul_pos hm ht)).mpr (by nlinarith [hr])
  apply (div_le_iff₀ (by positivity : 0 < (N : ℝ) ^ 2)).mpr
  have he : 2 * (N : ℝ) / ((Mass K : ℝ) * Cutoff K) * (N : ℝ) ^ 2 =
      2 * (N : ℝ) ^ 3 / ((Mass K : ℝ) * Cutoff K) := by ring
  rw [he]
  exact hc

#print axioms long_mass_arithmetic
#print axioms cutoff_arithmetic
#print axioms mass_pos
#print axioms actual_far_joint_bound
#print axioms actual_far_cubic_nat
#print axioms actual_far_normalized

end
end JSP233.FarJoint113
