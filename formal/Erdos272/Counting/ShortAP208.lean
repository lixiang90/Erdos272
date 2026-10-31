import Erdos272.Counting.APCount41

/-! Actual short progressions in the original ground set. The argument
counts prescribed root positions and prescribed pairs before using the
common-point / no-common-point dichotomy. -/
namespace JSP233.ShortAP208
open StarCompletion APGeometry APCount41
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

def RootPosition (c : ℤ) (S : Finset ℤ) : ℕ := Index (Low S) c (Step S)

theorem singleton_of_root_card_le_one {S : Finset ℤ} {c : ℤ}
    (hc : c ∈ S) (hcard : S.card ≤ 1) : S = {c} := by
  ext x
  constructor
  · intro hx
    exact Finset.mem_singleton.mpr (Finset.card_le_one.mp hcard x hx c hc)
  · intro hx
    exact (Finset.mem_singleton.mp hx).symm ▸ hc

theorem actual_AP_range {S : Finset ℤ} (hAP : IsAP S) :
    S = (Finset.range S.card).image
      (fun j : ℕ => Low S + (Step S : ℤ) * (j : ℤ)) := by
  obtain ⟨_, p, hp⟩ := actual_step hAP
  have hne := isAP_nonempty hAP
  simpa only [Low, dif_pos hne] using apAt_eq_range hp hne

theorem actual_root_position {N : ℕ} {S : Finset ℤ} {c : ℤ}
    (hsub : S ⊆ Ground N) (hAP : IsAP S) (htwo : 2 ≤ S.card) (hc : c ∈ S) :
    0 < Step S ∧ RootPosition c S < S.card ∧
      Low S + (RootPosition c S : ℤ) * (Step S : ℤ) = c ∧
      High S = Low S + ((S.card - 1 : ℕ) : ℤ) * (Step S : ℤ) := by
  obtain ⟨hd, p, hp⟩ := actual_step hAP
  have hne : S.Nonempty := ⟨c, hc⟩
  have hl := low_spec hne
  have hb := high_spec hne
  have hi := index_equation (hl.2 c hc) (apAt_dvd_sub hp hl.1 hc)
  have hspan := apAt_span_eq hp hne
  have hcb := hb.2 c hc
  have hLow : Low S = S.min' hne := by simp only [Low, dif_pos hne]
  have hHigh : High S = S.max' hne := by simp only [High, dif_pos hne]
  rw [← hLow, ← hHigh] at hspan
  have hipos : RootPosition c S < S.card := by
    have hdZ : (0 : ℤ) < Step S := by exact_mod_cast hd
    change Low S + (RootPosition c S : ℤ) * (Step S : ℤ) = c at hi
    have hh : (RootPosition c S : ℤ) < S.card := by nlinarith
    exact_mod_cast hh
  have hcast : ((S.card - 1 : ℕ) : ℤ) = (S.card : ℤ) - 1 := by
    have hh : 0 < S.card := Finset.card_pos.mpr hne
    omega
  refine ⟨hd, hipos, hi, ?_⟩
  rw [hcast]
  nlinarith only [hspan]

theorem actual_rooted_three_position_count {N i bound : ℕ}
    {F : Finset (Finset ℤ)} {c : ℤ}
    (hsub : ∀ S ∈ F, S ⊆ Ground N) (hAP : ∀ S ∈ F, IsAP S)
    (hthree : ∀ S ∈ F, S.card = 3) (hroot : ∀ S ∈ F, c ∈ S)
    (hposition : ∀ S ∈ F, RootPosition c S = i)
    (hbound : ∀ S ∈ F, Step S ≤ bound) : F.card ≤ bound := by
  have hdata := fun S hS => actual_root_position (hsub S hS) (hAP S hS)
    (by rw [hthree S hS]; omega) (hroot S hS)
  have hmaps : Set.MapsTo Step (F : Set (Finset ℤ)) (Finset.Icc 1 bound) := by
    intro S hS
    exact Finset.mem_Icc.mpr ⟨(hdata S hS).1, hbound S hS⟩
  have hinj : Set.InjOn Step (F : Set (Finset ℤ)) := by
    intro S hS T hT hd
    have hs := (hdata S hS).2.2.1
    have ht := (hdata T hT).2.2.1
    rw [hposition S hS, hd] at hs
    rw [hposition T hT] at ht
    have hlo : Low S = Low T := by omega
    have hsrepr := actual_AP_range (hAP S hS)
    have htrepr := actual_AP_range (hAP T hT)
    calc
      S = (Finset.range S.card).image
          (fun j : ℕ => Low S + (Step S : ℤ) * (j : ℤ)) := hsrepr
      _ = (Finset.range T.card).image
          (fun j : ℕ => Low T + (Step T : ℤ) * (j : ℤ)) := by
        rw [hthree S hS, hthree T hT, hlo, hd]
      _ = T := htrepr.symm
  have hh := Finset.card_le_card_of_injOn Step hmaps hinj
  simpa only [Nat.card_Icc, Nat.add_sub_cancel] using hh

theorem actual_rooted_three_AP_count {N : ℕ} {F : Finset (Finset ℤ)} {c : ℤ}
    (hc : c ∈ Ground N) (hsub : ∀ S ∈ F, S ⊆ Ground N)
    (hAP : ∀ S ∈ F, IsAP S) (hthree : ∀ S ∈ F, S.card = 3)
    (hroot : ∀ S ∈ F, c ∈ S) : F.card ≤ N - 1 := by
  let r := c.toNat
  have hcN := (mem_ground N c).mp hc
  have hrc : (r : ℤ) = c := Int.toNat_of_nonneg (by omega)
  have hr : 1 ≤ r ∧ r ≤ N := by omega
  let C (i : ℕ) := F.filter (fun S => RootPosition c S = i)
  have hdata := fun S hS => actual_root_position (hsub S hS) (hAP S hS)
    (by rw [hthree S hS]; omega) (hroot S hS)
  have hend : ∀ S ∈ F, (1 : ℤ) ≤ Low S ∧ High S ≤ (N : ℤ) := by
    intro S hS
    have hne := isAP_nonempty (hAP S hS)
    exact ⟨((mem_ground N (Low S)).mp (hsub S hS (low_spec hne).1)).1,
      ((mem_ground N (High S)).mp (hsub S hS (high_spec hne).1)).2⟩
  have hstep : ∀ i ∈ Finset.range 3, ∀ S ∈ C i,
      Step S ≤ if i = 0 then (N - r) / 2 else
        if i = 1 then min (r - 1) (N - r) else (r - 1) / 2 := by
    intro i hi S hS
    obtain ⟨hSF, hSi⟩ := Finset.mem_filter.mp hS
    obtain ⟨_, _, hs, he⟩ := hdata S hSF
    have hl := (hend S hSF).1
    have hh := (hend S hSF).2
    rw [hSi] at hs
    rw [hthree S hSF] at he
    norm_num at he
    have hir : i < 3 := Finset.mem_range.mp hi
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl
    · simp only [ite_true, Nat.cast_zero, zero_mul, add_zero] at hs ⊢
      have hbound : 2 * Step S ≤ N - r := by omega
      omega
    · simp only [show (1 : ℕ) ≠ 0 by omega, ite_false, ite_true,
        Nat.cast_one, one_mul] at hs ⊢
      have hb1 : Step S ≤ r - 1 := by omega
      have hb2 : Step S ≤ N - r := by omega
      exact le_min hb1 hb2
    · simp only [show (2 : ℕ) ≠ 0 by omega, show (2 : ℕ) ≠ 1 by omega,
        ite_false, Nat.cast_ofNat] at hs ⊢
      have hbound : 2 * Step S ≤ r - 1 := by omega
      omega
  have hcount : ∀ i ∈ Finset.range 3, (C i).card ≤
      if i = 0 then (N - r) / 2 else
        if i = 1 then min (r - 1) (N - r) else (r - 1) / 2 := by
    intro i hi
    apply actual_rooted_three_position_count
      (fun S hS => hsub S (Finset.mem_filter.mp hS).1)
      (fun S hS => hAP S (Finset.mem_filter.mp hS).1)
      (fun S hS => hthree S (Finset.mem_filter.mp hS).1)
      (fun S hS => hroot S (Finset.mem_filter.mp hS).1)
      (fun S hS => (Finset.mem_filter.mp hS).2)
    exact hstep i hi
  have hpart : F.card = ∑ i ∈ Finset.range 3, (C i).card :=
    Finset.card_eq_sum_card_fiberwise (show Set.MapsTo (RootPosition c)
      (F : Set (Finset ℤ)) (Finset.range 3) from fun S hS =>
        Finset.mem_range.mpr (by have hh := (hdata S hS).2.1; rw [hthree S hS] at hh; omega))
  have h0 := hcount 0 (by simp)
  have h1 := hcount 1 (by simp)
  have h2 := hcount 2 (by simp)
  norm_num at h0 h1 h2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hpart
  have hm : min (r - 1) (N - r) ≤ r - 1 := min_le_left _ _
  have hm' : min (r - 1) (N - r) ≤ N - r := min_le_right _ _
  omega

theorem actual_rooted_two_count {N : ℕ} {F : Finset (Finset ℤ)} {c : ℤ}
    (hc : c ∈ Ground N) (hsub : ∀ S ∈ F, S ⊆ Ground N)
    (htwo : ∀ S ∈ F, S.card = 2) (hroot : ∀ S ∈ F, c ∈ S) :
    F.card ≤ N - 1 := by
  let X := {S // S ∈ F}
  have hex : ∀ S : X, ∃ a : ℤ, S.val = {c, a} ∧ a ≠ c ∧ a ∈ Ground N := by
    intro S
    obtain ⟨a, b, hab, he⟩ := Finset.card_eq_two.mp (htwo S.val S.property)
    have hcmem : c = a ∨ c = b := by
      simpa only [he, Finset.mem_insert, Finset.mem_singleton] using hroot S.val S.property
    rcases hcmem with rfl | rfl
    · refine ⟨b, he, hab.symm, ?_⟩
      exact hsub S.val S.property (by rw [he]; simp)
    · refine ⟨a, by simpa only [Finset.pair_comm] using he, hab, ?_⟩
      exact hsub S.val S.property (by rw [he]; simp)
  choose a ha using hex
  have hmaps : Set.MapsTo a (Finset.univ : Finset X) ((Ground N).erase c) := by
    intro S _
    exact Finset.mem_erase.mpr ⟨(ha S).2.1, (ha S).2.2⟩
  have hinj : Function.Injective a := by
    intro S T he
    apply Subtype.ext
    rw [(ha S).1, (ha T).1, he]
  have hh := Finset.card_le_card_of_injOn a hmaps hinj.injOn
  have he := Finset.card_erase_add_one hc
  rw [ground_card] at he
  have hh' : F.card ≤ ((Ground N).erase c).card := by
    simpa only [Finset.card_univ, X, Fintype.card_coe] using hh
  omega

theorem actual_rooted_small_AP_count {N : ℕ} {F : Finset (Finset ℤ)} {c : ℤ}
    (hc : c ∈ Ground N) (hsub : ∀ S ∈ F, S ⊆ Ground N)
    (hAP : ∀ S ∈ F, IsAP S) (hcard : ∀ S ∈ F, S.card ≤ 3)
    (hroot : ∀ S ∈ F, c ∈ S) : F.card ≤ 2 * N - 1 := by
  let C (k : ℕ) := F.filter (fun S => S.card = k)
  have h1 : (C 1).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro S hS T hT
    obtain ⟨hSF, hSc⟩ := Finset.mem_filter.mp hS
    obtain ⟨hTF, hTc⟩ := Finset.mem_filter.mp hT
    rw [singleton_of_root_card_le_one (hroot S hSF) (by omega),
      singleton_of_root_card_le_one (hroot T hTF) (by omega)]
  have h2 : (C 2).card ≤ N - 1 := actual_rooted_two_count hc
    (fun S hS => hsub S (Finset.mem_filter.mp hS).1)
    (fun S hS => (Finset.mem_filter.mp hS).2)
    (fun S hS => hroot S (Finset.mem_filter.mp hS).1)
  have h3 : (C 3).card ≤ N - 1 := actual_rooted_three_AP_count hc
    (fun S hS => hsub S (Finset.mem_filter.mp hS).1)
    (fun S hS => hAP S (Finset.mem_filter.mp hS).1)
    (fun S hS => (Finset.mem_filter.mp hS).2)
    (fun S hS => hroot S (Finset.mem_filter.mp hS).1)
  have hcover : F ⊆ C 1 ∪ C 2 ∪ C 3 := by
    intro S hS
    have hp : 0 < S.card := Finset.card_pos.mpr ⟨c, hroot S hS⟩
    have hu := hcard S hS
    simp only [Finset.mem_union, C, Finset.mem_filter, hS, true_and]
    omega
  have hh := (Finset.card_le_card hcover).trans
    ((Finset.card_union_le (C 1 ∪ C 2) (C 3)).trans
      (Nat.add_le_add_right (Finset.card_union_le (C 1) (C 2)) _))
  have hN := (mem_ground N c).mp hc
  omega

theorem actual_three_AP_pair_completions {N : ℕ} {S : Finset ℤ} {a b : ℤ}
    (hsub : S ⊆ Ground N) (hAP : IsAP S) (hthree : S.card = 3)
    (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) :
    S = {a, b, 2 * a - b} ∨ S = {a, b, (a + b) / 2} ∨
      S = {a, b, 2 * b - a} := by
  have hr := actual_AP_range hAP
  rw [hthree] at hr
  have hre : S = {Low S, Low S + (Step S : ℤ), Low S + 2 * (Step S : ℤ)} := by
    calc
      S = (Finset.range 3).image (fun i : ℕ => Low S + (Step S : ℤ) * (i : ℤ)) := hr
      _ = _ := by
        ext x
        norm_num [show Finset.range 3 = {0, 1, 2} from by decide]
        omega
  rw [hre] at ha hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
  · exact False.elim (hab rfl)
  · right; right
    apply hre.trans
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  · right; left
    apply hre.trans
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  · left
    apply hre.trans
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  · exact False.elim (hab rfl)
  · left
    apply hre.trans
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  · right; left
    apply hre.trans
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  · right; right
    apply hre.trans
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  · exact False.elim (hab rfl)

def PairLibrary (a b : ℤ) : Finset (Finset ℤ) :=
  {{a, b}, {a, b, 2 * a - b}, {a, b, (a + b) / 2}, {a, b, 2 * b - a}}

theorem actual_short_AP_pair_library {N : ℕ} {S : Finset ℤ} {a b : ℤ}
    (hsub : S ⊆ Ground N) (hAP : IsAP S) (hsmall : S.card ≤ 3)
    (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) : S ∈ PairLibrary a b := by
  have hpair : ({a, b} : Finset ℤ) ⊆ S :=
    Finset.insert_subset_iff.mpr ⟨ha, Finset.singleton_subset_iff.mpr hb⟩
  have hlower : 2 ≤ S.card := by
    have hh := Finset.card_le_card hpair
    simpa only [Finset.card_pair hab] using hh
  by_cases htwo : S.card = 2
  · have he : S = {a, b} :=
      (Finset.eq_of_subset_of_card_le hpair (by simp [htwo, Finset.card_pair hab])).symm
    simp only [PairLibrary, Finset.mem_insert, Finset.mem_singleton]
    exact Or.inl he
  · have hthree : S.card = 3 := by omega
    have hc := actual_three_AP_pair_completions hsub hAP hthree ha hb hab
    simp only [PairLibrary, Finset.mem_insert, Finset.mem_singleton]
    exact Or.inr hc

theorem pair_library_card (a b : ℤ) : (PairLibrary a b).card ≤ 4 := by
  have h1 := Finset.card_insert_le ({a, b} : Finset ℤ)
    {{a, b, 2 * a - b}, {a, b, (a + b) / 2}, {a, b, 2 * b - a}}
  have h2 := Finset.card_insert_le ({a, b, 2 * a - b} : Finset ℤ)
    {{a, b, (a + b) / 2}, {a, b, 2 * b - a}}
  have h3 := Finset.card_insert_le ({a, b, (a + b) / 2} : Finset ℤ)
    {{a, b, 2 * b - a}}
  simp only [Finset.card_singleton] at h3
  dsimp only [PairLibrary]
  omega

theorem actual_short_AP_pair_count {N : ℕ} {F : Finset (Finset ℤ)} {a b : ℤ}
    (hsub : ∀ S ∈ F, S ⊆ Ground N) (hAP : ∀ S ∈ F, IsAP S)
    (hsmall : ∀ S ∈ F, S.card ≤ 3) (ha : ∀ S ∈ F, a ∈ S)
    (hb : ∀ S ∈ F, b ∈ S) (hab : a ≠ b) : F.card ≤ 4 := by
  have hs : F ⊆ PairLibrary a b := fun S hS =>
    actual_short_AP_pair_library (hsub S hS) (hAP S hS) (hsmall S hS)
      (ha S hS) (hb S hS) hab
  exact (Finset.card_le_card hs).trans (pair_library_card a b)

theorem actual_small_AP_family_count {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 19 ≤ N) (hF : Legal (Ground N) F)
    (hAP : ∀ S ∈ F, IsAP S) (hsmall : ∀ S ∈ F, S.card ≤ 3) :
    F.card ≤ 2 * N - 1 := by
  by_cases hne : F.Nonempty
  · obtain ⟨S₀, hS₀⟩ := hne
    by_cases hcommon : ∃ c : ℤ, ∀ S ∈ F, c ∈ S
    · obtain ⟨c, hc⟩ := hcommon
      exact actual_rooted_small_AP_count (hF.1 S₀ hS₀ (hc S₀ hS₀)) hF.1 hAP hsmall hc
    · let D (a : ℤ) := F.filter (fun S => a ∈ S)
      have hD : ∀ a ∈ S₀, (D a).card ≤ 12 := by
        intro a _ha₀
        have hex : ∃ B ∈ F, a ∉ B := by
          by_contra hh
          apply hcommon
          refine ⟨a, ?_⟩
          intro B hB
          by_contra haB
          exact hh ⟨B, hB, haB⟩
        obtain ⟨B, hB, haB⟩ := hex
        let E (b : ℤ) := (D a).filter (fun S => b ∈ S)
        have hE : ∀ b ∈ B, (E b).card ≤ 4 := by
          intro b hb
          apply actual_short_AP_pair_count
            (fun S hS => hF.1 S (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).1)
            (fun S hS => hAP S (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).1)
            (fun S hS => hsmall S (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).1)
            (fun S hS => (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).2)
            (fun S hS => (Finset.mem_filter.mp hS).2)
          intro he
          exact haB (he.symm ▸ hb)
        have hcover : D a ⊆ B.biUnion E := by
          intro S hS
          obtain ⟨hSF, haS⟩ := Finset.mem_filter.mp hS
          have hSB : S ≠ B := by intro he; exact haB (he ▸ haS)
          obtain ⟨b, hb⟩ := isAP_nonempty (hF.2 S hSF B hB hSB)
          obtain ⟨hbS, hbB⟩ := Finset.mem_inter.mp hb
          exact Finset.mem_biUnion.mpr
            ⟨b, hbB, Finset.mem_filter.mpr ⟨hS, hbS⟩⟩
        calc
          (D a).card ≤ (B.biUnion E).card := Finset.card_le_card hcover
          _ ≤ ∑ b ∈ B, (E b).card := Finset.card_biUnion_le
          _ ≤ ∑ _b ∈ B, 4 := Finset.sum_le_sum hE
          _ = B.card * 4 := by simp
          _ ≤ 12 := by have hh := Nat.mul_le_mul_right 4 (hsmall B hB); omega
      have hcover : F ⊆ S₀.biUnion D := by
        intro S hS
        have hh : (S₀ ∩ S).Nonempty := by
          by_cases he : S₀ = S
          · simpa only [he, Finset.inter_self] using isAP_nonempty (hAP S hS)
          · exact isAP_nonempty (hF.2 S₀ hS₀ S hS he)
        obtain ⟨a, ha⟩ := hh
        obtain ⟨ha₀, haS⟩ := Finset.mem_inter.mp ha
        exact Finset.mem_biUnion.mpr ⟨a, ha₀, Finset.mem_filter.mpr ⟨hS, haS⟩⟩
      have hcount : F.card ≤ 36 := by
        calc
          F.card ≤ (S₀.biUnion D).card := Finset.card_le_card hcover
          _ ≤ ∑ a ∈ S₀, (D a).card := Finset.card_biUnion_le
          _ ≤ ∑ _a ∈ S₀, 12 := Finset.sum_le_sum hD
          _ = S₀.card * 12 := by simp
          _ ≤ 36 := by have hh := Nat.mul_le_mul_right 12 (hsmall S₀ hS₀); omega
      omega
  · have he : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp only [he, Finset.card_empty, Nat.zero_le]

#print axioms actual_AP_range
#print axioms actual_root_position
#print axioms actual_rooted_three_position_count
#print axioms actual_rooted_three_AP_count
#print axioms actual_rooted_two_count
#print axioms actual_rooted_small_AP_count
#print axioms actual_three_AP_pair_completions
#print axioms actual_short_AP_pair_library
#print axioms pair_library_card
#print axioms actual_short_AP_pair_count
#print axioms actual_small_AP_family_count
end
end JSP233.ShortAP208
