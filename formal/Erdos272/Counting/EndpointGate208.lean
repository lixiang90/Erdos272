module

public import Erdos272.Counting.EndpointAP208
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

namespace JSP233.EndpointGate208
open StarCompletion HarmonicAbel29 EndpointAP208
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 20000

theorem scaled_harmonic_le (G U : ℕ) :
    (FastDivSum G U : ℝ) ≤ (G : ℝ) * Harmonic U := by
  calc
    (FastDivSum G U : ℝ) = ∑ d ∈ Finset.Icc 1 U, ((G / d : ℕ) : ℝ) := by
      exact_mod_cast fast_div_sum_eq G U
    _ ≤ ∑ d ∈ Finset.Icc 1 U, (G : ℝ) / d :=
      Finset.sum_le_sum (fun d _hd => Nat.cast_div_le (α := ℝ) (m := G) (n := d))
    _ = (G : ℝ) * Harmonic U := by
      simp only [Harmonic, div_eq_mul_inv, ← Finset.mul_sum, one_mul]

def Payment (U : ℕ) : ℝ := (U : ℝ) * (Harmonic U - 48 / 25) + 11

theorem payment_succ {n : ℕ} (hn : 1 ≤ n) : Payment n ≤ Payment (n + 1) := by
  have hrec : Harmonic (n + 1) = Harmonic n + 1 / ((n : ℝ) + 1) := by
    simp only [Harmonic]
    rw [Finset.sum_Icc_succ_top (by omega)]
    push_cast
    rfl
  have hH := harmonic_mono hn
  have hOne : Harmonic 1 = 1 := by norm_num [Harmonic]
  rw [hOne] at hH
  have hinv : ((n : ℝ) + 1) * (1 / ((n : ℝ) + 1)) = 1 := by field_simp
  dsimp only [Payment]
  rw [hrec]
  push_cast
  nlinarith only [hH, hinv]

theorem payment_mono {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    Payment a ≤ Payment b := by
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ b hab ih => exact ih.trans (payment_succ (ha.trans hab))

theorem integer_endpoint_bound {G a b h : ℕ} (hG : 0 < G)
    (hfloor : (h : ℝ) ≤ (G : ℝ) * Harmonic a)
    (hgate : 25 * G * FastEndpointCount (b - 1) + 48 * a * G ≤
      25 * a * h + 275 * G) :
    (EndpointCount (b - 1) : ℝ) ≤ Payment a := by
  have hgR : (0 : ℝ) < G := by exact_mod_cast hG
  have hgateR : 25 * (G : ℝ) * FastEndpointCount (b - 1) + 48 * (a : ℝ) * G ≤
      25 * (a : ℝ) * h + 275 * G := by exact_mod_cast hgate
  rw [fast_endpoint_count_eq] at hgateR
  have hm := mul_le_mul_of_nonneg_left hfloor (show (0 : ℝ) ≤ 25 * a by positivity)
  have ht : 25 * (G : ℝ) * EndpointCount (b - 1) + 48 * (a : ℝ) * G ≤
      25 * (a : ℝ) * ((G : ℝ) * Harmonic a) + 275 * G := by
    nlinarith only [hgateR, hm]
  have hmul : (G : ℝ) * (25 * EndpointCount (b - 1) + 48 * (a : ℝ)) ≤
      (G : ℝ) * (25 * (a : ℝ) * Harmonic a + 275) := by
    convert ht using 1 <;> ring
  have hc := le_of_mul_le_mul_left hmul hgR
  dsimp only [Payment]
  nlinarith only [hc]

theorem block_sound {G a b h U : ℕ} (hG : 0 < G) (ha : 1 ≤ a)
    (haU : a ≤ U) (hUb : U ≤ b)
    (hfloor : (h : ℝ) ≤ (G : ℝ) * Harmonic a)
    (hgate : 25 * G * FastEndpointCount (b - 1) + 48 * a * G ≤
      25 * a * h + 275 * G) :
    (EndpointCount (U - 1) : ℝ) ≤ Payment U := by
  have hm : (EndpointCount (U - 1) : ℝ) ≤ EndpointCount (b - 1) := by
    exact_mod_cast endpoint_count_mono (Nat.sub_le_sub_right hUb 1)
  exact hm.trans ((integer_endpoint_bound hG hfloor hgate).trans (payment_mono ha haU))

def FastIntervalSum (G lo : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => FastIntervalSum G lo n + G / (lo + n)

theorem fast_div_sum_add (G a len : ℕ) :
    FastDivSum G (a + len) = FastDivSum G a + FastIntervalSum G (a + 1) len := by
  induction len with
  | zero => simp [FastIntervalSum]
  | succ len ih =>
    change FastDivSum G ((a + len) + 1) = FastDivSum G a +
      (FastIntervalSum G (a + 1) len + G / ((a + 1) + len))
    rw [FastDivSum, ih]
    have he : a + 1 + len = a + len + 1 := by omega
    rw [he]
    omega

def EndpointCountAt (t root : ℕ) : ℕ :=
  2 * FastDivSum t root - root^2 - t - t / 2

theorem endpoint_count_at_eq {t root : ℕ}
    (hroot : root^2 ≤ t) (hnext : t < (root + 1)^2) :
    EndpointCountAt t root = EndpointCount t := by
  have h := Hyperbola131.actual_hyperbola_nat hroot hnext
  rw [← endpoint_divisor_identity, ← fast_div_sum_eq] at h
  dsimp only [EndpointCountAt]
  omega

structure Row where
  last : ℕ
  root : ℕ
  nextH : ℕ
  deriving DecidableEq, Repr

def RowCondition (G a h : ℕ) (r : Row) : Prop :=
  1 ≤ a ∧ a ≤ r.last ∧
  r.root^2 ≤ r.last - 1 ∧ r.last - 1 < (r.root + 1)^2 ∧
  25 * G * EndpointCountAt (r.last - 1) r.root + 48 * a * G ≤ 25 * a * h + 275 * G ∧
  r.nextH = h + FastIntervalSum G (a + 1) (r.last + 1 - a)

instance rowConditionDecidable (G a h : ℕ) (r : Row) : Decidable (RowCondition G a h r) :=
  inferInstanceAs (Decidable (1 ≤ a ∧ a ≤ r.last ∧
    r.root^2 ≤ r.last - 1 ∧ r.last - 1 < (r.root + 1)^2 ∧
    25 * G * EndpointCountAt (r.last - 1) r.root + 48 * a * G ≤ 25 * a * h + 275 * G ∧
    r.nextH = h + FastIntervalSum G (a + 1) (r.last + 1 - a)))

def CheckRows (G : ℕ) : ℕ → ℕ → List Row → Bool
  | _, _, [] => true
  | a, h, r :: rs => decide (RowCondition G a h r) && CheckRows G (r.last + 1) r.nextH rs

def RowsEnd : ℕ → ℕ → List Row → ℕ × ℕ
  | a, h, [] => (a, h)
  | _, _, r :: rs => RowsEnd (r.last + 1) r.nextH rs

theorem checked_rows_sound {G a h : ℕ} {rows : List Row} (hG : 0 < G)
    (hprefix : h = FastDivSum G a) (hchecked : CheckRows G a h rows = true) :
    (∀ U : ℕ, a ≤ U → U < (RowsEnd a h rows).1 →
      (EndpointCount (U - 1) : ℝ) ≤ Payment U) ∧
      (RowsEnd a h rows).2 = FastDivSum G (RowsEnd a h rows).1 := by
  induction rows generalizing a h with
  | nil =>
    constructor
    · intro U haU hU
      simp only [RowsEnd] at hU
      omega
    · simpa only [RowsEnd] using hprefix
  | cons r rs ih =>
    have hb : decide (RowCondition G a h r) = true ∧
        CheckRows G (r.last + 1) r.nextH rs = true := by
      simpa only [CheckRows, Bool.and_eq_true] using hchecked
    have hr : RowCondition G a h r := of_decide_eq_true hb.1
    obtain ⟨ha, halast, hroot, hrootnext, hgate, hnext⟩ := hr
    have hgate' : 25 * G * FastEndpointCount (r.last - 1) + 48 * a * G ≤
        25 * a * h + 275 * G := by
      rw [fast_endpoint_count_eq]
      rw [endpoint_count_at_eq hroot hrootnext] at hgate
      exact hgate
    have hpref' : r.nextH = FastDivSum G (r.last + 1) := by
      have ht := fast_div_sum_add G a (r.last + 1 - a)
      have he : a + (r.last + 1 - a) = r.last + 1 := by omega
      rw [he] at ht
      rw [hnext, hprefix]
      exact ht.symm
    obtain ⟨hbound, hfinal⟩ := ih hpref' hb.2
    constructor
    · intro U haU hU
      by_cases hlast : U ≤ r.last
      · have hfloor : (h : ℝ) ≤ (G : ℝ) * Harmonic a := by
          rw [hprefix]
          exact scaled_harmonic_le G a
        exact block_sound hG ha haU hlast hfloor hgate'
      · apply hbound U (by omega)
        simpa only [RowsEnd] using hU
    · simpa only [RowsEnd] using hfinal

#print axioms scaled_harmonic_le
#print axioms payment_mono
#print axioms integer_endpoint_bound
#print axioms block_sound
#print axioms fast_div_sum_add
#print axioms endpoint_count_at_eq
#print axioms checked_rows_sound
end
end JSP233.EndpointGate208
