module

public import Erdos272.Foundation.EightAPStencil
public import Erdos272.Foundation.PrivateUnion

@[expose] public section

/-!
The dyadic eight-member stencil payment theorem.
This file composes the genuine integer-set stencil theorem and the actual
AP-union/private-point theorem. The AP definition bridge is proved below.
-/

namespace JSP233.DyadicStencil

theorem two_dvd_or_coprime (g : Nat) : 2 ∣ g ∨ Nat.Coprime g 2 := by
  have hpos := Nat.gcd_pos_of_pos_right g (by decide : 0 < 2)
  have hle := Nat.gcd_le_right g (by decide : 0 < 2)
  by_cases h : Nat.gcd g 2 = 1
  · exact Or.inr h
  · have he : Nat.gcd g 2 = 2 := by omega
    exact Or.inl (he ▸ Nat.gcd_dvd_left g 2)

theorem dyadic_divisor_unique (a g : Nat) (hg0 : 0 < g)
    (hg : g ∣ 2^(a+1)) (hn : ¬ g ∣ 2^a) : g = 2^(a+1) := by
  induction a generalizing g with
  | zero =>
    have hb : g ≤ 2 := Nat.le_of_dvd (by decide) (by simpa using hg)
    have hone : g ≠ 1 := by intro h; subst g; simp at hn
    simp only [Nat.zero_add, Nat.pow_one]
    omega
  | succ a ih =>
    rcases two_dvd_or_coprime g with heven | hcop
    · rcases heven with ⟨k, rfl⟩
      have hk : 0 < k := by omega
      have hsmall : k ∣ 2^(a+1) := by
        apply Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 2)
        simpa [Nat.pow_succ, Nat.mul_comm] using hg
      have hnsmall : ¬ k ∣ 2^a := by
        intro h
        apply hn
        have hh := Nat.mul_dvd_mul_left 2 h
        simpa [Nat.pow_succ, Nat.mul_comm] using hh
      have heq := ih k hk hsmall hnsmall
      simp only [heq, Nat.pow_succ, Nat.mul_comm]
    · apply False.elim
      apply hn
      apply hcop.dvd_of_dvd_mul_right
      simpa [Nat.pow_succ] using hg

def step (j : Nat) : Int := (2^j : Nat)

theorem step_pos (j : Nat) : 0 < step j := by
  have h := Nat.pow_pos (n := j) (by decide : 0 < 2)
  unfold step
  omega

theorem step_double (j : Nat) : step (j+1) = 2 * step j := by
  simp only [step, Nat.pow_succ, Int.natCast_mul]
  omega

theorem step_four (j : Nat) : step (j+2) = 4 * step j := by
  rw [show j+2 = (j+1)+1 by omega, step_double, step_double]
  omega

theorem dyadic_divisor_unique_int (j : Nat) (q : Int) (hq : 0 < q)
    (hdiv : q ∣ 4 * step j) (hnot : ¬ q ∣ 2 * step j) :
    q = 4 * step j := by
  have hqnat : (q.natAbs : Int) = q := Int.natAbs_of_nonneg (Int.le_of_lt hq)
  have hqpos : 0 < q.natAbs := Int.natAbs_pos.mpr (by omega)
  have hdnat : q.natAbs ∣ 2^((j+1)+1) := by
    apply Int.ofNat_dvd_right.mp
    change q ∣ step ((j+1)+1)
    rw [show (j+1)+1 = j+2 by omega, step_four]
    exact hdiv
  have hnnat : ¬ q.natAbs ∣ 2^(j+1) := by
    intro h
    have hh := Int.ofNat_dvd_right.mpr h
    change q ∣ step (j+1) at hh
    rw [step_double] at hh
    exact hnot hh
  have he := dyadic_divisor_unique (j+1) q.natAbs hqpos hdnat hnnat
  have hecast := congrArg (fun n : Nat => (n : Int)) he
  rw [hqnat] at hecast
  change q = step ((j+1)+1) at hecast
  rw [show (j+1)+1 = j+2 by omega, step_four] at hecast
  exact hecast

/-- The AP definitions in the two imported files are extensionally
equivalent. In particular, the private-point theorem's crooked premise is
not silently substituted by a different abstract AP predicate. -/
theorem isAP_iff_privateUnion (p : Int → Prop) :
    EightAPStencil.IsAP p ↔ PrivateUnion.IsAP p := by
  constructor
  · rintro ⟨⟨u, hu⟩, lo, hi, o, d, hd, hrep⟩
    have hAP : PrivateUnion.APAt d o p := ⟨hd, lo, hi, hrep⟩
    exact ⟨d, u, PrivateUnion.APAt_rebase d o u p hAP hu, hu⟩
  · rintro ⟨d, u, ⟨hd, lo, hi, hrep⟩, hu⟩
    exact ⟨⟨u, hu⟩, lo, hi, u, d, hd, hrep⟩

/-- A genuine AP containing the dyadic bridge and avoiding its midpoint
has forced actual step 4d, even when it has arbitrary off-grid points. -/
theorem bridge_forces_step (T : Int → Prop) (c : Int) (j : Nat)
    (hAP : EightAPStencil.IsAP T)
    (hl : T (c-2*step j)) (hr : T (c+2*step j)) (hroot : ¬ T c) :
    PrivateUnion.APAt (4*step j) (c-2*step j) T := by
  rcases hAP.2 with ⟨lo, hi, o, q, hq, hrep⟩
  have hl' := (hrep _).mp hl
  have hr' := (hrep _).mp hr
  have hdiv := Int.dvd_sub hr'.2.2 hl'.2.2
  have he : (c+2*step j-o)-(c-2*step j-o) = 4*step j := by omega
  rw [he] at hdiv
  have hnot : ¬ q ∣ 2*step j := by
    intro hh
    have hmid := Int.dvd_add hh hl'.2.2
    have he' : 2*step j+(c-2*step j-o)=c-o := by omega
    rw [he'] at hmid
    apply hroot
    exact (hrep c).mpr ⟨by have := step_pos j; omega,
      by have := step_pos j; omega, hmid⟩
  have hqeq := dyadic_divisor_unique_int j q hq hdiv hnot
  have hat : PrivateUnion.APAt q o T := ⟨hq, lo, hi, hrep⟩
  rw [hqeq] at hat
  exact PrivateUnion.APAt_rebase (4*step j) o (c-2*step j) T hat hl

theorem actual_stencil_bridge
    (F : (Int → Prop) → Prop) (hlegal : EightAPStencil.Legal F)
    (A : Int → Prop) (hA : F A) (c : Int) (j : Nat)
    (hroot : ¬ A c)
    (hstencils : ∀ s : Fin 8,
      F (EightAPStencil.onGrid c (step j) (EightAPStencil.stencil s))) :
    A (c-2*step j) ∧ A (c+2*step j) := by
  have h := EightAPStencil.actual_family_stencil_contains_bridge
    F hlegal A hA c (step j) (step_pos j) hroot hstencils
  have hl : EightAPStencil.affine c (step j) 4 = c-2*step j := by
    simp [EightAPStencil.affine]
    omega
  have hr : EightAPStencil.affine c (step j) 8 = c+2*step j := by
    simp [EightAPStencil.affine]
    omega
  simpa only [hl, hr] using h

/-- End-to-end dyadic eight-member payment for actual crooked omitters.
The ground and core are actual lists of integer points; the core list may
be the full common intersection. The pair step is derived, not assumed.
The conclusion has no postulated scalar capacity inequality as a premise.
-/
theorem actual_stencil_add_core_le_ground_length {m : Nat}
    (F : (Int → Prop) → Prop) (hlegal : EightAPStencil.Legal F)
    (D : Fin m → Int → Prop) (hD : ∀ i, F (D i))
    (hDinj : ∀ i j, D i = D j → i = j)
    (c : Int) (j : Nat) (ground core : List Int) (hm : 2 ≤ m)
    (hroot : ∀ i, ¬ D i c)
    (hcrooked : ∀ i, ¬ EightAPStencil.IsAP (D i))
    (hstencils : ∀ s : Fin 8,
      F (EightAPStencil.onGrid c (step j) (EightAPStencil.stencil s)))
    (hground : ∀ i x, D i x → x ∈ ground)
    (hcore : ∀ x ∈ core, ∀ i, D i x) (hcore_nodup : core.Nodup) :
    m + core.length ≤ ground.length := by
  have hb := fun i => actual_stencil_bridge F hlegal (D i) (hD i) c j
    (hroot i) hstencils
  apply PrivateUnion.family_add_kernel_le_ground_length
    (4*step j) (c-2*step j) D ground core hm
  · intro i hi
    exact hcrooked i ((isAP_iff_privateUnion (D i)).mpr hi)
  · intro i
    exact (hb i).1
  · intro a b hab
    have hne : D a ≠ D b := by intro h; exact hab (hDinj a b h)
    apply bridge_forces_step (fun x => D a x ∧ D b x) c j
      (hlegal (D a) (D b) (hD a) (hD b) hne)
    · exact ⟨(hb a).1, (hb b).1⟩
    · exact ⟨(hb a).2, (hb b).2⟩
    · intro h
      exact hroot a h.1
  · exact hground
  · exact hcore
  · exact hcore_nodup

/-- If the actual ground contains the omitted root, that root is removed
from the available point list inside the proof, giving the sharper
`h+k ≤ N-1` form. Ground duplication is not needed as an extra hypothesis.
-/
theorem actual_stencil_add_core_lt_ground_length {m : Nat}
    (F : (Int → Prop) → Prop) (hlegal : EightAPStencil.Legal F)
    (D : Fin m → Int → Prop) (hD : ∀ i, F (D i))
    (hDinj : ∀ i j, D i = D j → i = j)
    (c : Int) (j : Nat) (ground core : List Int) (hm : 2 ≤ m)
    (hroot : ∀ i, ¬ D i c)
    (hcrooked : ∀ i, ¬ EightAPStencil.IsAP (D i))
    (hstencils : ∀ s : Fin 8,
      F (EightAPStencil.onGrid c (step j) (EightAPStencil.stencil s)))
    (hground : ∀ i x, D i x → x ∈ ground) (hcground : c ∈ ground)
    (hcore : ∀ x ∈ core, ∀ i, D i x) (hcore_nodup : core.Nodup) :
    m + core.length + 1 ≤ ground.length := by
  have hext : ∀ i x, D i x → x ∈ ground.erase c := by
    intro i x hx
    have hne : x ≠ c := by intro heq; subst x; exact hroot i hx
    exact (List.mem_erase_of_ne hne).mpr (hground i x hx)
  have h := actual_stencil_add_core_le_ground_length F hlegal D hD hDinj
    c j (ground.erase c) core hm hroot hcrooked hstencils hext hcore hcore_nodup
  have hlen := List.length_erase_of_mem hcground
  have hpos := List.length_pos_of_mem hcground
  omega

#print axioms dyadic_divisor_unique
#print axioms dyadic_divisor_unique_int
#print axioms isAP_iff_privateUnion
#print axioms bridge_forces_step
#print axioms actual_stencil_bridge
#print axioms actual_stencil_add_core_le_ground_length
#print axioms actual_stencil_add_core_lt_ground_length

end JSP233.DyadicStencil
