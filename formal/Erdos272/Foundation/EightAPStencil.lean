import Lean

/-!
The eight actual AP stencil, with an unbounded integer-set bridge.
The finite reflection uses only necessary arithmetic-closure rules, each
proved from a genuine positive-step, bounded congruence representation of
the actual intersection. No Boolean AP recognizer is trusted or assumed.
-/

namespace JSP233.EightAPStencil

def IsAP (p : Int → Prop) : Prop :=
  (∃ x, p x) ∧ ∃ lo hi origin step : Int,
    0 < step ∧ ∀ x, p x ↔ lo ≤ x ∧ x ≤ hi ∧ step ∣ x - origin

def affine (c d : Int) (i : Nat) : Int := c + d * ((i : Int) - 6)

def stencil : Fin 8 → List Nat
  | 0 => List.range 13
  | 1 => [3,4,5,6]
  | 2 => [6,7,8,9]
  | 3 => [4,5,6,7]
  | 4 => [5,6,7,8]
  | 5 => [2,4,6,8,10]
  | 6 => [0,3,6,9]
  | 7 => [3,6,9,12]

def onGrid (c d : Int) (s : List Nat) (x : Int) : Prop :=
  ∃ i, i ∈ s ∧ x = affine c d i

/-- True APs contain the gcd completion of any three of their points,
after any positive affine change of the integer coordinate. -/
theorem affine_AP_closed (p : Int → Prop) (c d : Int) (hd : 0 < d)
    (hap : IsAP p) (i j k x : Nat)
    (hix : i ≤ x) (hxk : x ≤ k)
    (hg : (Int.gcd ((j : Int)-i) ((k : Int)-i) : Int) ∣ (x : Int)-i)
    (hi : p (affine c d i)) (hj : p (affine c d j))
    (hk : p (affine c d k)) : p (affine c d x) := by
  rcases hap.2 with ⟨lo, hi', o, s, hs, hrep⟩
  have hpi := (hrep _).mp hi
  have hpj := (hrep _).mp hj
  have hpk := (hrep _).mp hk
  have hji := Int.dvd_sub hpj.2.2 hpi.2.2
  have hki := Int.dvd_sub hpk.2.2 hpi.2.2
  have ediff (a b : Nat) :
      (affine c d a-o)-(affine c d b-o) = d*((a : Int)-b) := by
    simp only [affine, Int.mul_sub]
    omega
  rw [ediff] at hji hki
  have hsg := Int.dvd_coe_gcd hji hki
  rw [Int.gcd_mul_left, Int.natCast_mul,
    Int.natAbs_of_nonneg (Int.le_of_lt hd)] at hsg
  have hsx := Int.dvd_trans hsg (Int.mul_dvd_mul_left d hg)
  have he : d*((x : Int)-i)+(affine c d i-o) = affine c d x-o := by
    simp only [affine, Int.mul_sub]
    omega
  have hso := Int.dvd_add hsx hpi.2.2
  rw [he] at hso
  have hleft := Int.mul_le_mul_of_nonneg_left
    (show (i : Int)-6 ≤ (x : Int)-6 by omega) (Int.le_of_lt hd)
  have hright := Int.mul_le_mul_of_nonneg_left
    (show (x : Int)-6 ≤ (k : Int)-6 by omega) (Int.le_of_lt hd)
  exact (hrep _).mpr ⟨by simp only [affine] at hpi ⊢; omega,
    by simp only [affine] at hpk ⊢; omega, hso⟩

structure Rule where
  i : Nat
  j : Nat
  k : Nat
  x : Nat
  deriving DecidableEq

/-- Nineteen sufficient rules selected from true three-point AP closure. -/
def rules : List Rule :=
  [⟨2,3,7,6⟩, ⟨4,5,9,6⟩, ⟨3,4,8,6⟩, ⟨0,5,8,6⟩,
   ⟨5,9,10,6⟩, ⟨0,4,7,6⟩, ⟨3,7,10,6⟩, ⟨4,8,9,5⟩,
   ⟨2,5,9,4⟩, ⟨3,5,8,4⟩, ⟨4,7,9,5⟩, ⟨3,7,8,4⟩,
   ⟨5,7,12,6⟩, ⟨3,4,7,6⟩, ⟨5,8,9,6⟩, ⟨0,1,4,3⟩,
   ⟨0,2,8,6⟩, ⟨0,4,10,2⟩, ⟨0,4,11,1⟩]

theorem rules_valid : ∀ r ∈ rules,
    r.i < 13 ∧ r.j < 13 ∧ r.k < 13 ∧ r.x < 13 ∧
    r.i ≤ r.x ∧ r.x ≤ r.k ∧
    (Int.gcd ((r.j : Int)-r.i) ((r.k : Int)-r.i) : Int) ∣ (r.x : Int)-r.i := by
  decide

theorem stencil_indices : ∀ s : Fin 8, ∀ i ∈ stencil s, i < 13 := by decide

def ruleOK (t : Nat → Bool) (r : Rule) : Bool :=
  if t r.i && t r.j && t r.k then t r.x else true

def compatible (t : Nat → Bool) : Bool :=
  !(t 6) &&
  ((List.finRange 8).all fun s => (stencil s).any t) &&
  (rules.all fun r => ruleOK t r)

def trace (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 : Bool) : Nat → Bool
  | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3 | 4 => b4 | 5 => b5 | 6 => b6
  | 7 => b7 | 8 => b8 | 9 => b9 | 10 => b10 | 11 => b11 | 12 => b12 | _ => false

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Exhaustion of all 8192 Boolean traces, including the excluded root bit. -/
theorem finite_classification :
    ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 : Bool,
    compatible (trace b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12) = true →
    ∀ i : Fin 13,
      trace b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 i.val =
        (i.val == 0 || i.val == 4 || i.val == 8 || i.val == 12) := by
  decide

theorem trace_agrees (t : Nat → Bool) (i : Nat) (hi : i < 13) :
    trace (t 0) (t 1) (t 2) (t 3) (t 4) (t 5) (t 6)
      (t 7) (t 8) (t 9) (t 10) (t 11) (t 12) i = t i := by
  have hc : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨
      i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 := by omega
  rcases hc with h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst i <;> rfl

theorem any_congr_mem (l : List α) (t u : α → Bool)
    (h : ∀ i ∈ l, t i = u i) : l.any t = l.any u := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.any_cons]
    rw [h a (by simp), ih (by intro i hi; exact h i (by simp [hi]))]

theorem all_congr_mem (l : List α) (t u : α → Bool)
    (h : ∀ i ∈ l, t i = u i) : l.all t = l.all u := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.all_cons]
    rw [h a (by simp), ih (by intro i hi; exact h i (by simp [hi]))]

theorem compatible_congr (t u : Nat → Bool)
    (htu : ∀ i, i < 13 → t i = u i) : compatible t = compatible u := by
  have hroot := htu 6 (by decide)
  have hnonempty : ∀ s : Fin 8, (stencil s).any t = (stencil s).any u := by
    intro s
    apply any_congr_mem
    intro i hi
    exact htu i (stencil_indices s i hi)
  have hrules : ∀ r ∈ rules, ruleOK t r = ruleOK u r := by
    intro r hr
    have hv := rules_valid r hr
    simp only [ruleOK, htu r.i hv.1, htu r.j hv.2.1,
      htu r.k hv.2.2.1, htu r.x hv.2.2.2.1]
  have hnall := List.all_congr (l₁ := List.finRange 8) rfl hnonempty
  have hrall := all_congr_mem rules (ruleOK t) (ruleOK u) hrules
  simp only [compatible, hroot, hnall, hrall]

/-- The genuinely unbounded result. The eight intersections are actual,
nonempty integer arithmetic progressions; A may have arbitrary off-grid
points. Positive d is arbitrary, and not assumed a power of two. -/
theorem integer_stencil_forces_trace (A : Int → Prop) (c d : Int)
    (hd : 0 < d) (hroot : ¬ A c)
    (hcompat : ∀ s : Fin 8,
      IsAP (fun x => A x ∧ onGrid c d (stencil s) x)) :
    ∀ i : Fin 13, A (affine c d i.val) ↔
      i.val = 0 ∨ i.val = 4 ∨ i.val = 8 ∨ i.val = 12 := by
  classical
  let t : Nat → Bool := fun i => decide (A (affine c d i))
  have ht : ∀ i, t i = true ↔ A (affine c d i) := by intro i; simp [t]
  have hz : t 6 = false := by simp [t, affine, hroot]
  have hn : (List.finRange 8).all (fun s => (stencil s).any t) = true := by
    apply List.all_eq_true.mpr
    intro s hs
    rcases (hcompat s).1 with ⟨x, hax, i, hi, hxi⟩
    apply List.any_eq_true.mpr
    exact ⟨i, hi, (ht i).mpr (hxi ▸ hax)⟩
  have hr : rules.all (ruleOK t) = true := by
    apply List.all_eq_true.mpr
    intro r hr
    have hv := rules_valid r hr
    have hinc (i : Nat) (hi : i < 13) (ha : t i = true) :
        A (affine c d i) ∧ onGrid c d (stencil 0) (affine c d i) := by
      exact ⟨(ht i).mp ha, i, by simpa [stencil] using hi, rfl⟩
    unfold ruleOK
    split
    next h =>
      have hh := Bool.and_eq_true_iff.mp h
      have hh' := Bool.and_eq_true_iff.mp hh.1
      exact (ht r.x).mpr (affine_AP_closed _ c d hd (hcompat 0)
        r.i r.j r.k r.x hv.2.2.2.2.1 hv.2.2.2.2.2.1 hv.2.2.2.2.2.2
        (hinc r.i hv.1 hh'.1) (hinc r.j hv.2.1 hh'.2)
        (hinc r.k hv.2.2.1 hh.2)).1
    next => rfl
  have hct : compatible t = true := by simp [compatible, hz, hn, hr]
  have hc := finite_classification (t 0) (t 1) (t 2) (t 3) (t 4) (t 5) (t 6)
    (t 7) (t 8) (t 9) (t 10) (t 11) (t 12)
  have hce : compatible
      (trace (t 0) (t 1) (t 2) (t 3) (t 4) (t 5) (t 6)
        (t 7) (t 8) (t 9) (t 10) (t 11) (t 12)) = true := by
    rw [compatible_congr _ t (trace_agrees t)]
    exact hct
  intro i
  have h := hc hce i
  rw [trace_agrees t i.val i.isLt] at h
  rw [← ht i.val, h]
  simp [or_assoc]

/-- The original pairwise-intersection legality condition. Individual
members are arbitrary integer predicates and need not themselves be APs. -/
def Legal (F : (Int → Prop) → Prop) : Prop :=
  ∀ A B, F A → F B → A ≠ B → IsAP (fun x => A x ∧ B x)

theorem stencil_contains_root (c d : Int) (s : Fin 8) :
    onGrid c d (stencil s) c := by
  have h : ∀ s : Fin 8, 6 ∈ stencil s := by decide
  exact ⟨6, h s, by simp [affine]⟩

/-- Full family interface: the stencil sets are actual members of the
legal family, not subwindows merely contained in other members. -/
theorem actual_family_stencil_forces_trace
    (F : (Int → Prop) → Prop) (hlegal : Legal F)
    (A : Int → Prop) (hA : F A) (c d : Int)
    (hd : 0 < d) (hroot : ¬ A c)
    (hstencils : ∀ s : Fin 8, F (onGrid c d (stencil s))) :
    ∀ i : Fin 13, A (affine c d i.val) ↔
      i.val = 0 ∨ i.val = 4 ∨ i.val = 8 ∨ i.val = 12 := by
  apply integer_stencil_forces_trace A c d hd hroot
  intro s
  apply hlegal A (onGrid c d (stencil s)) hA (hstencils s)
  intro heq
  apply hroot
  rw [heq]
  exact stencil_contains_root c d s

theorem actual_family_stencil_contains_bridge
    (F : (Int → Prop) → Prop) (hlegal : Legal F)
    (A : Int → Prop) (hA : F A) (c d : Int)
    (hd : 0 < d) (hroot : ¬ A c)
    (hstencils : ∀ s : Fin 8, F (onGrid c d (stencil s))) :
    A (affine c d 4) ∧ A (affine c d 8) := by
  have h := actual_family_stencil_forces_trace F hlegal A hA c d hd hroot hstencils
  exact ⟨(h 4).mpr (by decide), (h 8).mpr (by decide)⟩

#print axioms affine_AP_closed
#print axioms rules_valid
#print axioms finite_classification
#print axioms integer_stencil_forces_trace
#print axioms actual_family_stencil_forces_trace
#print axioms actual_family_stencil_contains_bridge

end JSP233.EightAPStencil
