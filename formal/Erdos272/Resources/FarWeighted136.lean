module

public import Erdos272.Resources.ActualJoint136
public import Erdos272.Resources.FarCut134

@[expose] public section
namespace JSP233.FarWeighted136
open StarCompletion APGeometry NearAP36 FarSlot112 FarCapacity112 FarJoint112
  FarShort112 FarFinal112 FarCut134
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

theorem actual_far_joint_bound_of_cut {N K t : ℕ} {F : Finset (Finset ℤ)}
    (hF : Legal (Ground N) F) (hK : 0 < K)
    (hsize : ∀ S ∈ F, 3 * K ≤ S.card)
    (hfar : ∀ S ∈ F, ¬ HasNearAPCore K S)
    (htK : K ≤ t) (ht : 1 ≤ t) (hM : t+1 ≤ 3*K)
    (hsq : Mass K ≤ (3*K-t)^2) :
    3 * Mass K * F.card ≤ 4 * ((N - 1) / t) * N ^ 2 := by
  let M := t + 1
  let D := (N - 1) / t
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
      apply FarJoint113.long_mass_arithmetic hK
      · dsimp [short, M] at hs
        omega
      · exact non_near_core_shell_mass (hmax S hS) (hsize S hS) (hfar S hS)
      · have heq := Finset.card_sdiff_add_card_eq_card (hcoords S hS).1.1
        have hh := hsize S hS
        omega
  exact ActualJoint136.actual_joint_count_maximum hF core step short
    (fun S hS=>(hcoords S hS).1) hAt hcut hmass

theorem actual_far_cubic_nat_of_cut {N K t:ℕ} {F:Finset (Finset ℤ)}
    (hF:Legal (Ground N) F) (hK:0<K)
    (hsize:∀S∈F,3*K≤S.card) (hfar:∀S∈F,¬HasNearAPCore K S)
    (htK:K≤t) (ht:1≤t) (hM:t+1≤3*K) (hsq:Mass K≤(3*K-t)^2) :
    3*Mass K*t*F.card≤4*N^3 := by
  have hj:=actual_far_joint_bound_of_cut hF hK hsize hfar htK ht hM hsq
  have hDt:((N-1)/t)*t≤N:=(Nat.div_mul_le_self (N-1) t).trans (Nat.sub_le N 1)
  calc
    _=(3*Mass K*F.card)*t:=by ring
    _≤(4*((N-1)/t)*N^2)*t:=Nat.mul_le_mul_right t hj
    _=(4*N^2)*(((N-1)/t)*t):=by ring
    _≤(4*N^2)*N:=Nat.mul_le_mul_left _ hDt
    _=4*N^3:=by ring

theorem actual_far_normalized_of_cut {N K t:ℕ} {F:Finset (Finset ℤ)}
    (hF:Legal (Ground N) F) (hK:0<K) (hN:0<N)
    (hsize:∀S∈F,3*K≤S.card) (hfar:∀S∈F,¬HasNearAPCore K S)
    (htK:K≤t) (ht:1≤t) (hM:t+1≤3*K) (hsq:Mass K≤(3*K-t)^2) :
    (F.card:ℝ)/(N:ℝ)^2≤4*(N:ℝ)/(3*(Mass K:ℝ)*t) := by
  have hh:=actual_far_cubic_nat_of_cut hF hK hsize hfar htK ht hM hsq
  have hr:3*(Mass K:ℝ)*t*(F.card:ℝ)≤4*(N:ℝ)^3:=by exact_mod_cast hh
  have hm:0<(Mass K:ℝ):=by exact_mod_cast FarCut134.mass_pos hK
  have htN:0<t:=by omega
  have htR:0<(t:ℝ):=by exact_mod_cast htN
  have hc:(F.card:ℝ)≤4*(N:ℝ)^3/(3*(Mass K:ℝ)*t):=
    (le_div_iff₀ (by positivity:0<3*(Mass K:ℝ)*t)).mpr (by nlinarith only [hr])
  apply (div_le_iff₀ (by positivity:0<(N:ℝ)^2)).mpr
  have he:4*(N:ℝ)/(3*(Mass K:ℝ)*t)*(N:ℝ)^2=4*(N:ℝ)^3/(3*(Mass K:ℝ)*t):=by ring
  rw [he]
  exact hc

theorem actual_far_normalized111 {N K:ℕ} {F:Finset (Finset ℤ)}
    (hF:Legal (Ground N) F) (hK:0<K) (hN:0<N)
    (hsize:∀S∈F,3*K≤S.card) (hfar:∀S∈F,¬HasNearAPCore K S) :
    (F.card:ℝ)/(N:ℝ)^2≤4*(N:ℝ)/(3*(Mass K:ℝ)*Cutoff K) := by
  obtain ⟨htK,ht,hM,hsq⟩:=FarCut134.cutoff_arithmetic hK
  exact actual_far_normalized_of_cut hF hK hN hsize hfar htK ht hM hsq

#print axioms actual_far_joint_bound_of_cut
#print axioms actual_far_cubic_nat_of_cut
#print axioms actual_far_normalized_of_cut
#print axioms actual_far_normalized111
end
end JSP233.FarWeighted136
