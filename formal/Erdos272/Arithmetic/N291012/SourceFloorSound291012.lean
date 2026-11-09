module

public import Erdos272.Arithmetic.N291012.PrefixComplete291012

@[expose] public section

namespace JSP233.SourceFloorSound291012
open PureSource208 SourceMoment291012 PrefixData291012
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def PartialValue (s e : ℕ) : ℕ :=
  if s < 2*e then FastSource208.fastPhysicalK FastDecode208.phi s e else Value p q s e

def Check (start len e b : ℕ) : Bool :=
  (List.range len).all fun j => decide (b ≤ PartialValue (start+j) e)

theorem partial_lower {s e : ℕ} (he : e ≤ s) (hs : s ≤ 29435) :
    PartialValue s e ≤ physicalK s e := by
  unfold PartialValue
  split_ifs
  · exact (FastSource208.fastPhysicalK_eq
      (fun n hn => FastDecode208.phi_correct n (hn.trans (by decide : 29435 ≤ 32753))) hs e).le
  · have h1 := PrefixComplete291012.table_correct s hs
    have h2 := PrefixComplete291012.table_correct (s-e) ((Nat.sub_le s e).trans hs)
    simpa only [Value, h1.1, h1.2, h2.1, h2.2] using value_lower he

theorem check_sound {start len e b s : ℕ}
    (hc : Check start len e b = true) (hlo : start ≤ s) (hhi : s < start+len)
    (he : e ≤ s) (hs : s ≤ 29435) : b ≤ physicalK s e := by
  have hj : s-start ∈ List.range len := by simp only [List.mem_range]; omega
  have hh := (List.all_eq_true.mp hc) (s-start) hj
  have heq : start+(s-start) = s := by omega
  have hb : b ≤ PartialValue s e := by simpa only [heq, decide_eq_true_eq] using hh
  exact hb.trans (partial_lower he hs)

def Floor (T e b : ℕ) : Prop := ∀ s, T ≤ s → s < 2^50 → b ≤ physicalK s e

theorem of_prefix_tail {T e b C : ℕ} (hT : 1 ≤ T) (he : e ≤ C)
    (htail : 7*b ≤ (C-e) * (e+1).choose 2)
    (hprefix : ∀ s, T ≤ s → s < C → b ≤ physicalK s e) : Floor T e b := by
  intro s hs hbig
  by_cases h : s < C
  · exact hprefix s hs h
  · exact TotientTail208.tail_floor (hT.trans hs) he (by omega) hbig htail

theorem extend_stronger {T U e b b' C : ℕ} (hT : 1 ≤ T) (he : e ≤ C)
    (htail : 7*b ≤ (C-e) * (e+1).choose 2)
    (hprefix : ∀ s, T ≤ s → s < min C U → b ≤ physicalK s e)
    (hstrong : b ≤ b') (hsuffix : Floor U e b') : Floor T e b := by
  intro s hs hbig
  by_cases hU : U ≤ s
  · exact hstrong.trans (hsuffix s hU hbig)
  · by_cases hC : C ≤ s
    · exact TotientTail208.tail_floor (hT.trans hs) he hC hbig htail
    · exact hprefix s hs (by omega)

theorem weaken {T U e b b' : ℕ} (hT : T ≤ U) (hb : b' ≤ b)
    (h : Floor T e b) : Floor U e b' :=
  fun s hs hbig => hb.trans (h s (hT.trans hs) hbig)

theorem physical_shift {l s d e : ℕ} (hls : l ≤ s) (hstart : s-e ≤ l-d) :
    physicalK l d ≤ physicalK s e := by
  apply (Finset.sum_le_sum (s := Finset.Ico (l-d) l)
    (fun q _ => Nat.mul_le_mul_left (Nat.totient q)
      (intervalMultiplicity_mono_size q hls))).trans
  apply Finset.sum_le_sum_of_subset
  intro q hq
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hq
  exact Finset.mem_Ico.mpr ⟨hstart.trans hlo, hhi.trans_le hls⟩

def CoverCheck (start finish e b : ℕ) : List ℕ → Bool
  | [] => decide (finish ≤ start)
  | stride :: rest =>
    decide (start ≤ 29435 ∧ 1 ≤ stride ∧ stride ≤ e ∧
      b ≤ PartialValue start (e+1-stride)) &&
      CoverCheck (start+stride) finish e b rest

theorem cover_sound {e b finish : ℕ} (strides : List ℕ) :
    ∀ start, e ≤ start → CoverCheck start finish e b strides = true →
      ∀ s, start ≤ s → s < finish → b ≤ physicalK s e := by
  induction strides with
  | nil =>
    intro start _ hc s hs hfinish
    have hh : finish ≤ start := of_decide_eq_true hc
    omega
  | cons stride rest ih =>
    intro start he hc s hs hfinish
    have hh : decide (start ≤ 29435 ∧ 1 ≤ stride ∧ stride ≤ e ∧
        b ≤ PartialValue start (e+1-stride)) = true ∧
        CoverCheck (start+stride) finish e b rest = true := by
      simpa only [CoverCheck, Bool.and_eq_true_iff] using hc
    obtain ⟨hstart, hstride, hstrideE, hvalue⟩ := of_decide_eq_true hh.1
    by_cases hnext : s < start+stride
    · have hp := hvalue.trans (partial_lower (by omega : e+1-stride ≤ start) hstart)
      exact hp.trans (physical_shift hs (by omega))
    · exact ih (start+stride) (by omega) hh.2 s (by omega) hfinish

theorem append_cover {lo mid hi e b : ℕ}
    (hleft : ∀ s, lo ≤ s → s < mid → b ≤ physicalK s e)
    (hright : ∀ s, mid ≤ s → s < hi → b ≤ physicalK s e) :
    ∀ s, lo ≤ s → s < hi → b ≤ physicalK s e := by
  intro s hs hhi
  by_cases hmid : s < mid
  · exact hleft s hs hmid
  · exact hright s (by omega) hhi

#print axioms partial_lower
#print axioms check_sound
#print axioms of_prefix_tail
#print axioms extend_stronger
#print axioms weaken
#print axioms physical_shift
#print axioms cover_sound
#print axioms append_cover
end
end JSP233.SourceFloorSound291012
