module

public import Erdos272.Resources.FarCapacity112
public import Erdos272.Retention.LongTerminal35
public import Mathlib.Data.Finset.Sort
public import Erdos272.Foundation.ProofTactics
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

/-! Actual Short-source geometry and its complete ordered gap supply.

The selected maximum AP is a real subset of the source.  No private-code
cardinality assumption or pre-supplied gap lower bound occurs in the source
theorems.  The anchor is allowed to vary with the actual adjacent gap.
-/
namespace JSP233.FarShort112
open StarCompletion APGeometry NearAP36 LongTerminal35 FarCapacity112
open scoped Classical BigOperators
noncomputable section

def Adjacent (S : Finset ℤ) (a b : ℤ) : Prop :=
  a ∈ S ∧ b ∈ S ∧ a < b ∧ ∀ x ∈ S, ¬ (a < x ∧ x < b)

theorem adjacent_AP_step {S A : Finset ℤ} {a b : ℤ}
    (hadj : Adjacent S a b) (hAS : A ⊆ S) (hAP : IsAP A)
    (ha : a ∈ A) (hb : b ∈ A) : APAt (b-a) a A := by
  obtain ⟨d, p, hAt, _⟩ := (isAP_iff_exists_APAt _).mp hAP
  have hd : 0 < d := hAt.1
  have hdiv : d ∣ b-a := apAt_dvd_sub hAt ha hb
  have hle : d ≤ b-a := Int.le_of_dvd (by have := hadj.2.2.1; omega) hdiv
  have he : d = b-a := by
    by_contra hne
    have hlt : d < b-a := lt_of_le_of_ne hle hne
    have hx : a+d ∈ A := apAt_fill hAt ha hb (by omega) (by omega)
      (by simp)
    exact hadj.2.2.2 (a+d) (hAS hx) ⟨by omega, by omega⟩
  simpa only [he] using apAt_rebase hAt ha

theorem adjacent_core_intrinsic {S R : Finset ℤ} {a b x : ℤ}
    (hadj : Adjacent S a b) (hR : MaximalAPCore S R)
    (ha : a ∈ R) (hb : b ∈ R) (hx : x ∈ S \ R) :
    IntrinsicPair a S {b,x} := by
  obtain ⟨hxS, hxR⟩ := Finset.mem_sdiff.mp hx
  have hbx : b ≠ x := by intro he; exact hxR (he ▸ hb)
  have hax : a ≠ x := by intro he; exact hxR (he ▸ ha)
  refine ⟨by simp [hbx], by simp [ne_of_lt hadj.2.2.1, hax], ?_, ?_⟩
  · intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hadj.2.1
    · exact hxS
  · rintro ⟨A, hA, hsub, hAS⟩
    have haA : a ∈ A := hsub (by simp)
    have hbA : b ∈ A := hsub (by simp)
    have hxA : x ∈ A := hsub (by simp)
    have hAd := adjacent_AP_step hadj hAS hA haA hbA
    have hRd := adjacent_AP_step hadj hR.1 hR.2.1 ha hb
    have hu : APAt (b-a) a (R ∪ A) := by
      simpa only [APAt, Finset.mem_union] using
        PrivateUnion.union_APAt (b-a) a (fun z => z ∈ R) (fun z => z ∈ A) hRd hAd ha haA
    have huAP : IsAP (R ∪ A) := (isAP_iff_exists_APAt _).mpr
      ⟨b-a, a, hu, Finset.mem_union_left _ ha⟩
    have he := hR.2.2 (R ∪ A) Finset.subset_union_left (Finset.union_subset hR.1 hAS) huAP
    exact hxR (he ▸ Finset.mem_union_right R hxA)

theorem actual_adjacent_intrinsic_mass {S P : Finset ℤ} {a b : ℤ}
    (hmax : MaximumAPCore S P) (hadj : Adjacent S a b) :
    S.card - P.card ≤ (S.filter (fun x => IntrinsicPair a S {b,x})).card := by
  have hpair : ({a,b} : Finset ℤ) ⊆ S := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hadj.1
    · exact hadj.2.1
  obtain ⟨R, hpairR, hR⟩ := actual_maximal_AP_extension hpair (pair_isAP a b)
  have ha : a ∈ R := hpairR (by simp)
  have hb : b ∈ R := hpairR (by simp)
  have hcard : R.card ≤ P.card := hmax.2.2 R hR.1 hR.2.1
  have hsub : S \ R ⊆ S.filter (fun x => IntrinsicPair a S {b,x}) := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hx).1,
      adjacent_core_intrinsic hadj hR ha hb hx⟩
  have hs := Finset.card_le_card hsub
  rw [Finset.card_sdiff_of_subset hR.1] at hs
  exact (Nat.sub_le_sub_left hcard S.card).trans hs

def point (S : Finset ℤ) (i : ℕ) : ℤ :=
  if h : i < S.card then S.orderEmbOfFin rfl ⟨i,h⟩ else 0
def gap (S : Finset ℤ) (i : ℕ) : ℤ := point S (i+1) - point S i
def SmallGaps (S : Finset ℤ) (D : ℕ) : Finset ℕ :=
  (Finset.range (S.card-1)).filter (fun i => gap S i ≤ (D : ℤ))
def LargeGaps (S : Finset ℤ) (D : ℕ) : Finset ℕ :=
  (Finset.range (S.card-1)).filter (fun i => (D : ℤ) < gap S i)

theorem point_mem {S : Finset ℤ} {i : ℕ} (hi : i < S.card) : point S i ∈ S := by
  simp only [point, dif_pos hi]
  exact S.orderEmbOfFin_mem rfl ⟨i,hi⟩

theorem point_strict {S : Finset ℤ} {i j : ℕ} (hi : i < j) (hj : j < S.card) :
    point S i < point S j := by
  have hiS : i < S.card := lt_trans hi hj
  simp only [point, dif_pos hiS, dif_pos hj]
  exact (S.orderEmbOfFin rfl).strictMono (show (⟨i,hiS⟩ : Fin S.card) < ⟨j,hj⟩ from hi)

theorem actual_adjacent_gap {S : Finset ℤ} {i : ℕ} (hi : i < S.card-1) :
    Adjacent S (point S i) (point S (i+1)) := by
  have hiS : i < S.card := by omega
  have hi1S : i+1 < S.card := by omega
  refine ⟨point_mem hiS, point_mem hi1S, point_strict (by omega) hi1S, ?_⟩
  intro x hx hbetween
  let j : Fin S.card := (S.orderIsoOfFin rfl).symm ⟨x,hx⟩
  have hjx : S.orderEmbOfFin rfl j = x := by
    exact congrArg Subtype.val ((S.orderIsoOfFin rfl).apply_symm_apply ⟨x,hx⟩)
  have hpoint : point S j.val = x := by simpa only [point, dif_pos j.isLt] using hjx
  have hleft : i < j.val := by
    by_contra hle
    have hh : point S j.val ≤ point S i := by
      simp only [point, dif_pos j.isLt, dif_pos hiS]
      exact (S.orderEmbOfFin rfl).monotone (show j ≤ ⟨i,hiS⟩ by change j.val ≤ i; omega)
    omega
  have hright : j.val < i+1 := by
    by_contra hle
    have hh : point S (i+1) ≤ point S j.val := by
      simp only [point, dif_pos j.isLt, dif_pos hi1S]
      exact (S.orderEmbOfFin rfl).monotone
        (show (⟨i+1,hi1S⟩ : Fin S.card) ≤ j by change i+1 ≤ j.val; omega)
    omega
  omega

theorem gap_pos {S : Finset ℤ} {i : ℕ} (hi : i < S.card-1) : 0 < gap S i := by
  have hh := (actual_adjacent_gap hi).2.2.1
  dsimp [gap]
  omega

theorem telescope (f : ℕ → ℤ) (k : ℕ) :
    ∑ i ∈ Finset.range k, (f (i+1) - f i) = f k - f 0 := by
  induction k with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; ring

theorem actual_gap_sum_bound {N : ℕ} {S : Finset ℤ}
    (hS : S ⊆ Ground N) (hne : S.Nonempty) :
    ∑ i ∈ Finset.range (S.card-1), gap S i ≤ (N : ℤ)-1 := by
  have hc : 0 < S.card := Finset.card_pos.mpr hne
  have hzero := (mem_ground N _).mp (hS (point_mem (show 0 < S.card from hc)))
  have hlast := (mem_ground N _).mp (hS (point_mem (show S.card-1 < S.card by omega)))
  have he := telescope (point S) (S.card-1)
  change (∑ i ∈ Finset.range (S.card-1), (point S (i+1)-point S i)) ≤ _
  rw [he]
  omega

theorem large_gap_card_bound {N M : ℕ} {S : Finset ℤ}
    (hS : S ⊆ Ground N) (hne : S.Nonempty) (hM : 2 ≤ M) :
    (LargeGaps S ((N-1)/(M-1))).card ≤ M-2 := by
  let D := (N-1)/(M-1)
  let E := LargeGaps S D
  have hN : 1 ≤ N := by
    obtain ⟨x,hx⟩ := hne
    have := (mem_ground N x).mp (hS hx)
    omega
  have hm : 0 < M-1 := by omega
  have hmod := Nat.mod_lt (N-1) hm
  have hdiv := Nat.mod_add_div (N-1) (M-1)
  have hstrict : N-1 < (D+1)*(M-1) := by dsimp [D]; nlinarith
  have hstrictZ : (N : ℤ)-1 < ((D : ℤ)+1)*((M : ℤ)-1) := by
    have hh : ((N-1 : ℕ) : ℤ) < (((D+1)*(M-1) : ℕ) : ℤ) := by exact_mod_cast hstrict
    simpa only [Nat.cast_sub hN, Nat.cast_sub (by omega : 1 ≤ M),
      Nat.cast_mul, Nat.cast_add, Nat.cast_one] using hh
  have hmass : (E.card : ℤ) * ((D : ℤ)+1) ≤ ∑ i ∈ E, gap S i := by
    calc
      _ = ∑ _i ∈ E, ((D : ℤ)+1) := by simp
      _ ≤ _ := Finset.sum_le_sum (by
        intro i hi
        have hh := (Finset.mem_filter.mp hi).2
        change (D : ℤ) < gap S i at hh
        omega)
  have hsub : E ⊆ Finset.range (S.card-1) := by
    exact Finset.filter_subset _ _
  have hsum : (∑ i ∈ E, gap S i) ≤ ∑ i ∈ Finset.range (S.card-1), gap S i := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (by
      intro i hi _
      exact (gap_pos (Finset.mem_range.mp hi)).le)
  have hbound := actual_gap_sum_bound hS hne
  have hlong : (E.card : ℤ) < (M : ℤ)-1 := by
    by_contra hh
    have hmul := mul_le_mul_of_nonneg_right (show (M : ℤ)-1 ≤ E.card by omega)
      (show (0 : ℤ) ≤ (D : ℤ)+1 by positivity)
    nlinarith
  change (LargeGaps S D).card ≤ M-2
  change (E.card : ℕ) ≤ M-2
  omega

theorem actual_small_gap_card {N M : ℕ} {S : Finset ℤ}
    (hS : S ⊆ Ground N) (hM : 2 ≤ M) (hcard : M ≤ S.card) :
    S.card-M+1 ≤ (SmallGaps S ((N-1)/(M-1))).card := by
  have hne : S.Nonempty := Finset.card_pos.mp (by omega)
  have hlong := large_gap_card_bound hS hne hM
  have hpart := Finset.card_filter_add_card_filter_not (s:=Finset.range (S.card-1))
    (fun i => gap S i ≤ (((N-1)/(M-1) : ℕ) : ℤ))
  have he : (Finset.range (S.card-1)).filter
      (fun i => ¬ gap S i ≤ (((N-1)/(M-1) : ℕ) : ℤ)) = LargeGaps S ((N-1)/(M-1)) := by
    ext i
    simp [LargeGaps]
  rw [he, Finset.card_range] at hpart
  change (SmallGaps S ((N-1)/(M-1))).card +
    (LargeGaps S ((N-1)/(M-1))).card = S.card-1 at hpart
  omega

def ShortInputs (S : Finset ℤ) (D : ℕ) : Finset (Σ _ : ℕ, ℤ) :=
  (SmallGaps S D).sigma (fun i =>
    S.filter (fun x => IntrinsicPair (point S i) S {point S (i+1),x}))

def shortCode (S : Finset ℤ) (q : Σ _ : ℕ, ℤ) : ℕ × (ℤ × ℤ) :=
  ((gap S q.1).toNat, (point S q.1, q.2))

def ShortCodes (S : Finset ℤ) (D : ℕ) : Finset (ℕ × (ℤ × ℤ)) :=
  (ShortInputs S D).image (shortCode S)

theorem point_injective {S : Finset ℤ} {i j : ℕ} (hi : i < S.card)
    (hj : j < S.card) (he : point S i = point S j) : i = j := by
  simp only [point, dif_pos hi, dif_pos hj] at he
  have hh := (S.orderEmbOfFin rfl).injective he
  exact congrArg Fin.val hh

theorem shortCode_injective {S : Finset ℤ} {D : ℕ} :
    Set.InjOn (shortCode S) (ShortInputs S D) := by
  rintro ⟨i,x⟩ hi ⟨j,y⟩ hj he
  have hiGap := (Finset.mem_sigma.mp hi).1
  have hjGap := (Finset.mem_sigma.mp hj).1
  change i ∈ SmallGaps S D at hiGap
  change j ∈ SmallGaps S D at hjGap
  have hiS : i < S.card := by
    have hh := Finset.mem_range.mp (Finset.mem_filter.mp hiGap).1
    omega
  have hjS : j < S.card := by
    have hh := Finset.mem_range.mp (Finset.mem_filter.mp hjGap).1
    omega
  have hij : i = j := point_injective hiS hjS (congrArg (fun q => q.2.1) he)
  have hxy : x = y := congrArg (fun q => q.2.2) he
  cases hij
  cases hxy
  rfl

theorem shortCodes_card {S : Finset ℤ} {D : ℕ} :
    (ShortCodes S D).card = ∑ i ∈ SmallGaps S D,
      (S.filter (fun x => IntrinsicPair (point S i) S {point S (i+1),x})).card := by
  rw [ShortCodes, Finset.card_image_of_injOn shortCode_injective, ShortInputs, Finset.card_sigma]

theorem actual_short_codes {N D : ℕ} {S : Finset ℤ} (hS : S ⊆ Ground N)
    {q : ℕ × (ℤ × ℤ)} (hq : q ∈ ShortCodes S D) :
    q ∈ PhysicalSlots N D ∧ q.2.1 ∈ S ∧
      IntrinsicPair q.2.1 S {q.2.1 + (q.1 : ℤ), q.2.2} := by
  obtain ⟨⟨i,x⟩, hi, rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨hiGap, hx⟩ := Finset.mem_sigma.mp hi
  obtain ⟨hiRange, hiD⟩ := Finset.mem_filter.mp hiGap
  have hi0 := Finset.mem_range.mp hiRange
  change i < S.card-1 at hi0
  change gap S i ≤ (D : ℤ) at hiD
  obtain ⟨hxS, hIntrinsic⟩ := Finset.mem_filter.mp hx
  have hg := gap_pos hi0
  have hcast : (((gap S i).toNat : ℕ) : ℤ) = gap S i := Int.toNat_of_nonneg hg.le
  have hd : 1 ≤ (gap S i).toNat := by omega
  have hdD : (gap S i).toNat ≤ D := by omega
  have haS := point_mem (show i < S.card by omega)
  have hnext : point S i + (((gap S i).toNat : ℕ) : ℤ) = point S (i+1) := by
    rw [hcast]
    dsimp [gap]
    omega
  refine ⟨?_, haS, ?_⟩
  · apply Finset.mem_product.mpr
    exact ⟨Finset.mem_Icc.mpr ⟨hd,hdD⟩, Finset.mem_product.mpr ⟨hS haS,hS hxS⟩⟩
  · change IntrinsicPair (point S i) S {point S i + (((gap S i).toNat : ℕ) : ℤ), x}
    simpa only [hnext] using hIntrinsic

theorem actual_short_source_mass {N M : ℕ} {S P : Finset ℤ}
    (hS : S ⊆ Ground N) (hmax : MaximumAPCore S P)
    (hM : 2 ≤ M) (hcard : M ≤ S.card) (hshort : P.card < M) :
    (S.card-M+1)^2 ≤ (ShortCodes S ((N-1)/(M-1))).card := by
  have hgap := actual_small_gap_card hS hM hcard
  have hper : S.card-M+1 ≤ S.card-P.card := by omega
  have hsum : (SmallGaps S ((N-1)/(M-1))).card * (S.card-P.card) ≤
      (ShortCodes S ((N-1)/(M-1))).card := by
    rw [shortCodes_card]
    calc
      _ = ∑ _i ∈ SmallGaps S ((N-1)/(M-1)), (S.card-P.card) := by simp
      _ ≤ _ := Finset.sum_le_sum (by
        intro i hi
        have hindex := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
        exact actual_adjacent_intrinsic_mass hmax (actual_adjacent_gap hindex))
  have hp := Nat.mul_le_mul hgap hper
  simpa only [pow_two] using hp.trans hsum

#print axioms adjacent_AP_step
#print axioms adjacent_core_intrinsic
#print axioms actual_adjacent_intrinsic_mass
#print axioms point_mem
#print axioms point_strict
#print axioms actual_adjacent_gap
#print axioms gap_pos
#print axioms telescope
#print axioms actual_gap_sum_bound
#print axioms large_gap_card_bound
#print axioms actual_small_gap_card
#print axioms point_injective
#print axioms shortCode_injective
#print axioms shortCodes_card
#print axioms actual_short_codes
#print axioms actual_short_source_mass
end
end JSP233.FarShort112
