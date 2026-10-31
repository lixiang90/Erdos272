import Erdos272.Resources.PairEnvelope208

/-! Exact cardinal saving from the coarse residue subsequence of a finer AP. -/
namespace JSP233.PairSlice208
open StarCompletion APGeometry SourceBridge208 PairEnvelope208
open scoped Classical
noncomputable section
set_option maxHeartbeats 0

theorem slice_card {U : Finset ℤ} {d a : ℤ} {q : ℕ}
    (hU : APAt d a U) (ha : a ∈ U) (hq : 0 < q) :
    U.card / q ≤ (CoarseSlice U (d*q) a).card := by
  have hne : U.Nonempty := ⟨a, ha⟩
  let c := U.min' hne
  let b := U.max' hne
  have hc : c ∈ U := Finset.min'_mem U hne
  have hb : b ∈ U := Finset.max'_mem U hne
  have hca : c ≤ a := Finset.min'_le U a ha
  have hd : 0 < d := hU.1
  have hdiv : d ∣ a-c := apAt_dvd_sub hU hc ha
  let rZ : ℤ := (a-c)/d
  have hrZ0 : 0 ≤ rZ := Int.ediv_nonneg (by omega) hd.le
  have hrEq : d*rZ = a-c := by
    dsimp only [rZ]
    nlinarith only [Int.ediv_mul_cancel hdiv]
  let r : ℕ := rZ.toNat
  have hr : (r : ℤ) = rZ := Int.toNat_of_nonneg hrZ0
  have hphase : d*(r : ℤ) = a-c := by rw [hr]; exact hrEq
  let f : ℕ → ℤ := fun j => c + d * (((r % q + q*j : ℕ) : ℤ))
  have hqZ : (0 : ℤ) < q := by exact_mod_cast hq
  have hinj : Function.Injective f := by
    intro j k he
    dsimp only [f] at he
    push_cast at he
    have hfirst := mul_left_cancel₀ (ne_of_gt hd) (add_left_cancel he)
    have hsecond := add_left_cancel hfirst
    have hjk : (j : ℤ) = k := mul_left_cancel₀ (ne_of_gt hqZ) hsecond
    exact_mod_cast hjk
  have hsub : (Finset.range (U.card/q)).image f ⊆ CoarseSlice U (d*q) a := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    have hjq : j < U.card/q := Finset.mem_range.mp hj
    have hrem : r%q < q := Nat.mod_lt r hq
    have hdivle : q*(U.card/q) ≤ U.card := Nat.mul_div_le _ _
    have hjle : q*(j+1) ≤ q*(U.card/q) := Nat.mul_le_mul_left q (by omega)
    have hidx : r%q+q*j < U.card := by nlinarith
    have hidxZ : ((r%q+q*j : ℕ) : ℤ) < U.card := by exact_mod_cast hidx
    have hidx0 : (0 : ℤ) ≤ (r%q+q*j : ℕ) := by positivity
    have hspan : b-c = d*((U.card : ℤ)-1) := apAt_span_eq hU hne
    have hlo : c ≤ f j := by
      dsimp only [f]
      exact le_add_of_nonneg_right (mul_nonneg hd.le hidx0)
    have hhi : f j ≤ b := by
      have hm := mul_le_mul_of_nonneg_left (by omega : ((r%q+q*j : ℕ) : ℤ) ≤ (U.card : ℤ)-1) hd.le
      dsimp only [f]
      nlinarith only [hspan, hm]
    have hfU : f j ∈ U := apAt_fill hU hc hb hlo hhi
      ⟨(r%q+q*j : ℕ), by dsimp only [f]; ring⟩
    apply Finset.mem_filter.mpr
    refine ⟨hfU, ?_⟩
    have hmodN := Nat.mod_add_div r q
    have hmodZ : ((r%q : ℕ) : ℤ) + (q : ℤ)*(r/q : ℕ) = r := by
      exact_mod_cast hmodN
    refine ⟨(j : ℤ)-(r/q : ℕ), ?_⟩
    dsimp only [f]
    push_cast
    calc
      c + d * ((r%q : ℕ) + (q : ℤ)*j) - a =
          d * (((r%q : ℕ) : ℤ) + (q : ℤ)*j-r) := by nlinarith only [hphase]
      _ = (d*(q : ℤ))*((j : ℤ)-(r/q : ℕ)) := by
        rw [show (((r%q : ℕ) : ℤ) + (q : ℤ)*j-r) =
          (q : ℤ)*((j : ℤ)-(r/q : ℕ)) by nlinarith only [hmodZ]]
        ring
  have hh := Finset.card_le_card hsub
  simpa only [Finset.card_image_of_injective _ hinj, Finset.card_range] using hh

theorem subtraction_div_monotone {q : ℕ} (hq : 0 < q) :
    Monotone (fun n : ℕ => n-n/q) := by
  apply monotone_nat_of_le_succ
  intro n
  have hdiv : (n+1)/q ≤ n/q+1 := by
    have hh := Nat.div_le_div_right (c := q) (by omega : n+1 ≤ n+q)
    simpa only [Nat.add_div_right _ hq] using hh
  omega

/-- The actual fine envelope contributes only its noncoarse points. -/
theorem extra_card {S U : Finset ℤ} {a b d : ℤ} {q m : ℕ}
    (hUS : U ⊆ S) (hU : APAt d a U) (ha : a ∈ U) (hb : b ∈ U)
    (hab : a < b) (hD : b-a = d*q) (hq : 0 < q) (hm : U.card ≤ m) :
    (U \ Envelope S (b-a) a b).card ≤ m-m/q := by
  have hs := coarseSlice_subset_envelope hUS hU ha hb hab hD
  have hsub : CoarseSlice U (b-a) a ⊆ U ∩ Envelope S (b-a) a b := by
    intro x hx
    exact Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp hx).1, hs hx⟩
  have hcard := Finset.card_le_card hsub
  have hc := slice_card hU ha hq
  rw [← hD] at hc
  have he := Finset.card_sdiff_add_card_inter U (Envelope S (b-a) a b)
  have hraw : (U \ Envelope S (b-a) a b).card ≤ U.card-U.card/q := by omega
  exact hraw.trans (subtraction_div_monotone hq hm)

#print axioms slice_card
#print axioms extra_card
end
end JSP233.PairSlice208
