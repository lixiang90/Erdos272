import Erdos272.Retention.JointFringe44
import Erdos272.Resources.ActualGrid208

/-! Actual aligned members may use a separate anchor quantum at every
physical step.  The private-point code retains the actual step and grid
index.  Its residue is recovered from the private point, so no factor of
the step is paid. -/
namespace JSP233.Aligned208
open StarCompletion APGeometry
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 20000

abbrev Key := Σ _d : ℕ, ℕ × ℕ

def Origin (q : ℕ → ℕ) (L : ℤ) (k : Key) : ℤ :=
  L - 1 + (k.2.1 : ℤ) + ((k.2.2 : ℤ) * q k.1 - 1) * k.1

def Keys (D : Finset ℕ) (p : ℕ → ℕ) : Finset Key :=
  D.sigma (fun d => (Finset.Icc 1 d).product (Finset.Icc 1 ((p d - 1) / d)))

def HasAnchor (q : ℕ → ℕ) (L R : ℤ) (k : Key) (S : Finset ℤ) : Prop :=
  APAt (k.1 : ℤ) (Origin q L k) (S ∩ Finset.Icc L R) ∧
    Origin q L k ∈ S ∩ Finset.Icc L R ∧
    Origin q L k + (k.1 : ℤ) ∈ S ∩ Finset.Icc L R

def Aligned (K : Finset ℤ → Key) (q : ℕ → ℕ) (L : ℤ) (S : Finset ℤ) : Prop :=
  ∀ y ∈ S, ((K S).1 : ℤ) ∣ y - Origin q L (K S)

def StepClass (E : Finset (Finset ℤ)) (K : Finset ℤ → Key) (d : ℕ) :
    Finset (Finset ℤ) := E.filter (fun S => (K S).1 = d)

def ResidueOutside (N : ℕ) (L R : ℤ) (d : ℕ) (a : ℤ) : Finset ℤ :=
  (Ground N \ Finset.Icc L R).filter (fun y => (d : ℤ) ∣ y - a)

def ResiduePool (D : Finset ℕ) (p : ℕ → ℕ) (O : ℕ → Finset ℤ) :
    Finset (Σ _d : ℕ, ℕ × ℤ) :=
  D.sigma (fun d => (Finset.Icc 1 ((p d - 1) / d)).product (O d))

theorem residue_pool_card (D : Finset ℕ) (p : ℕ → ℕ) (O : ℕ → Finset ℤ) :
    (ResiduePool D p O).card = ∑ d ∈ D, ((p d - 1) / d) * (O d).card := by
  simp [ResiduePool, Finset.card_sigma, Finset.card_product]

theorem origin_residue {q : ℕ → ℕ} {L y : ℤ} {k : Key}
    (h : (k.1 : ℤ) ∣ y - Origin q L k) :
    (k.1 : ℤ) ∣ (y - (L - 1)) - (k.2.1 : ℤ) := by
  have ho : (k.1 : ℤ) ∣ Origin q L k - (L - 1) - (k.2.1 : ℤ) := by
    refine ⟨(k.2.2 : ℤ) * q k.1 - 1, ?_⟩
    dsimp only [Origin]
    ring
  rw [show (y - (L - 1)) - (k.2.1 : ℤ) =
    (y - Origin q L k) + (Origin q L k - (L - 1) - (k.2.1 : ℤ)) by ring]
  exact dvd_add h ho

theorem actual_private_point {N : ℕ} {E : Finset (Finset ℤ)} {L R : ℤ}
    (K : Finset ℤ → Key) (q : ℕ → ℕ)
    (hlegal : Legal (Ground N) E) (hbad : ∀ S ∈ E, ¬ IsAP S)
    (hanchor : ∀ S ∈ E, HasAnchor q L R (K S) S) :
    ∀ S ∈ E, ∃ y, y ∈ S ∧ y ∉ Finset.Icc L R ∧
      ∀ T ∈ E, K T = K S → T ≠ S → y ∉ T := by
  intro S hS
  let C := E.filter (fun T => K T = K S)
  have hCS : S ∈ C := Finset.mem_filter.mpr ⟨hS, rfl⟩
  have hCE : C ⊆ E := Finset.filter_subset _ _
  have hc : ∀ T ∈ C, HasAnchor q L R (K S) T := by
    intro T hT
    have he := (Finset.mem_filter.mp hT).2
    simpa only [he] using hanchor T (hCE hT)
  obtain ⟨y, hy, hyI, hprivate⟩ := ThinFringe33.actual_class_private_point
    (fun T hT => hbad T (hCE hT))
    (fun T hT U hU hne => hlegal.2 T (hCE hT) U (hCE hU) hne)
    (fun T hT => (hc T hT).1) (fun T hT => (hc T hT).2.1)
    (fun T hT => (hc T hT).2.2) hCS
  exact ⟨y, hy, hyI, fun T hT he hne =>
    hprivate T (Finset.mem_filter.mpr ⟨hT, he⟩) hne⟩

theorem actual_step_common_residue {N d : ℕ} {E : Finset (Finset ℤ)}
    {K : Finset ℤ → Key} {q : ℕ → ℕ} {L : ℤ}
    (hlegal : Legal (Ground N) E) (halign : ∀ S ∈ E, Aligned K q L S) :
    ∃ a : ℤ, ∀ S ∈ StepClass E K d, ∀ y ∈ S, (d : ℤ) ∣ y - a := by
  let C := StepClass E K d
  by_cases hC : C.Nonempty
  · obtain ⟨T, hT⟩ := hC
    have hTE : T ∈ E := (Finset.mem_filter.mp hT).1
    have hTd : (K T).1 = d := (Finset.mem_filter.mp hT).2
    refine ⟨Origin q L (K T), ?_⟩
    intro S hS y hy
    have hSE : S ∈ E := (Finset.mem_filter.mp hS).1
    have hSd : (K S).1 = d := (Finset.mem_filter.mp hS).2
    by_cases he : S = T
    · subst S
      simpa only [hTd] using halign T hTE y hy
    · obtain ⟨z, hz⟩ := isAP_nonempty (hlegal.2 S hSE T hTE he)
      have hSy := halign S hSE y hy
      have hSz := halign S hSE z (Finset.mem_inter.mp hz).1
      have hTz := halign T hTE z (Finset.mem_inter.mp hz).2
      rw [hSd] at hSy hSz
      rw [hTd] at hTz
      rw [show y - Origin q L (K T) =
        (y - Origin q L (K S)) - (z - Origin q L (K S)) +
          (z - Origin q L (K T)) by ring]
      exact dvd_add (dvd_sub hSy hSz) hTz
  · exact ⟨0, fun S hS => False.elim (hC ⟨S, hS⟩)⟩

/-- All members and anchors are in the same original family and interval.
Different steps may use different quantum values in `q`. -/
theorem actual_count_from_anchors {N : ℕ} {E : Finset (Finset ℤ)} {L R : ℤ}
    (D : Finset ℕ) (p q : ℕ → ℕ) (K : Finset ℤ → Key)
    (hlegal : Legal (Ground N) E) (hbad : ∀ S ∈ E, ¬ IsAP S)
    (hD : ∀ d ∈ D, 0 < d) (hkeys : ∀ S ∈ E, K S ∈ Keys D p)
    (hanchor : ∀ S ∈ E, HasAnchor q L R (K S) S)
    (halign : ∀ S ∈ E, Aligned K q L S) :
    ∃ phase : ℕ → ℤ, E.card ≤ ∑ d ∈ D,
      ((p d - 1) / d) * (ResidueOutside N L R d (phase d)).card := by
  have hphases (d : ℕ) : ∃ a : ℤ,
      ∀ S ∈ StepClass E K d, ∀ y ∈ S, (d : ℤ) ∣ y - a :=
    actual_step_common_residue hlegal halign
  choose phase hphase using hphases
  have hex := actual_private_point K q hlegal hbad hanchor
  choose Y hY using hex
  let O : ℕ → Finset ℤ := fun d => ResidueOutside N L R d (phase d)
  have hc : E.card ≤ (ResiduePool D p O).card := by
    apply Finset.card_le_card_of_injective (f := fun S : E =>
      (⟨⟨(K S.val).1, (K S.val).2.2, Y S.val S.property⟩,
        Finset.mem_sigma.mpr ⟨(Finset.mem_sigma.mp (hkeys S.val S.property)).1,
          Finset.mem_product.mpr
            ⟨(Finset.mem_product.mp (Finset.mem_sigma.mp (hkeys S.val S.property)).2).2,
             Finset.mem_filter.mpr
              ⟨Finset.mem_sdiff.mpr
                ⟨hlegal.1 S.val S.property (hY S.val S.property).1,
                  (hY S.val S.property).2.1⟩,
               hphase (K S.val).1 S.val (Finset.mem_filter.mpr ⟨S.property, rfl⟩)
                 (Y S.val S.property) (hY S.val S.property).1⟩⟩⟩⟩ :
        ↥(ResiduePool D p O)))
    intro S T he
    apply Subtype.ext
    by_contra hne
    have hcode := congrArg Subtype.val he
    have hd : (K S.val).1 = (K T.val).1 :=
      congrArg (fun z : Σ _d : ℕ, ℕ × ℤ => z.1) hcode
    have hj : (K S.val).2.2 = (K T.val).2.2 :=
      congrArg (fun z : Σ _d : ℕ, ℕ × ℤ => z.2.1) hcode
    have hy : Y S.val S.property = Y T.val T.property :=
      congrArg (fun z : Σ _d : ℕ, ℕ × ℤ => z.2.2) hcode
    obtain ⟨hds, hrjs⟩ := Finset.mem_sigma.mp (hkeys S.val S.property)
    obtain ⟨hdt, hrjt⟩ := Finset.mem_sigma.mp (hkeys T.val T.property)
    have hrs := Finset.mem_Icc.mp (Finset.mem_product.mp hrjs).1
    have hrt := Finset.mem_Icc.mp (Finset.mem_product.mp hrjt).1
    have hresS := origin_residue (halign S.val S.property _ (hY S.val S.property).1)
    have hresT := origin_residue (halign T.val T.property _ (hY T.val T.property).1)
    rw [← hy, ← hd] at hresT
    have hrt' : 1 ≤ (K T.val).2.1 ∧ (K T.val).2.1 ≤ (K S.val).1 := by omega
    have hrho := JointFringe44.bounded_residue_eq (hD _ hds) hrs hrt' hresS hresT
    have hkEq : K S.val = K T.val := Sigma.ext hd (heq_of_eq (Prod.ext hrho hj))
    have hyT : Y S.val S.property ∈ T.val := by rw [hy]; exact (hY T.val T.property).1
    exact (hY S.val S.property).2.2 T.val T.property hkEq.symm (Ne.symm hne) hyT
  exact ⟨phase, hc.trans_eq (residue_pool_card D p O)⟩

def ResidueInterval (lo hi : ℤ) (d : ℕ) (a : ℤ) : Finset ℤ :=
  (Finset.Icc lo hi).filter (fun y => (d : ℤ) ∣ y - a)

theorem residue_interval_mass (lo hi a : ℤ) {d : ℕ} (hd : 0 < d) :
    d * (ResidueInterval lo hi d a).card ≤ (hi - lo + 1).toNat + (d - 1) := by
  let C := ResidueInterval lo hi d a
  change d * C.card ≤ (hi - lo + 1).toNat + (d - 1)
  by_cases hne : C.Nonempty
  · have hAP : APAt (d : ℤ) a C := by
      refine ⟨by exact_mod_cast hd, lo, hi, ?_⟩
      intro y
      simp only [C, ResidueInterval, Finset.mem_filter, Finset.mem_Icc]
      tauto
    have hspan := apAt_span_eq hAP hne
    have hlo := Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.min'_mem C hne)).1
    have hhi := Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.max'_mem C hne)).1
    have hn : ((hi - lo + 1).toNat : ℤ) = hi - lo + 1 := Int.toNat_of_nonneg (by omega)
    have hd1 : 1 ≤ d := by omega
    have hb : ((d * C.card : ℕ) : ℤ) ≤
        (((hi - lo + 1).toNat + (d - 1) : ℕ) : ℤ) := by
      rw [Nat.cast_mul, Nat.cast_add, Nat.cast_sub hd1, Nat.cast_one]
      nlinarith only [hspan, hlo.1, hhi.2, hn]
    exact_mod_cast hb
  · have he : C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    rw [he]
    simp

theorem residue_outside_mass {N L R d : ℕ}
    (hL : 1 ≤ L) (hLR : L ≤ R) (hRN : R ≤ N) (hd : 0 < d) (a : ℤ) :
    d * (ResidueOutside N (L : ℤ) (R : ℤ) d a).card ≤
      (L - 1) + (N - R) + 2 * (d - 1) := by
  let A := ResidueInterval 1 ((L : ℤ) - 1) d a
  let B := ResidueInterval ((R : ℤ) + 1) N d a
  have he : ResidueOutside N (L : ℤ) (R : ℤ) d a = A ∪ B := by
    ext y
    simp only [ResidueOutside, A, B, ResidueInterval, Finset.mem_filter,
      Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_union, mem_ground]
    omega
  have hdis : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro y ha hb
    have ha' := Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1
    have hb' := Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1
    omega
  have ha := residue_interval_mass 1 ((L : ℤ) - 1) a hd
  have hb := residue_interval_mass ((R : ℤ) + 1) N a hd
  have hleft : (((L : ℤ) - 1) - 1 + 1).toNat = L - 1 := by omega
  have hright : ((N : ℤ) - ((R : ℤ) + 1) + 1).toNat = N - R := by omega
  rw [hleft] at ha
  rw [hright] at hb
  rw [he, Finset.card_union_of_disjoint hdis, Nat.mul_add]
  change d * A.card + d * B.card ≤ (L - 1) + (N - R) + 2 * (d - 1)
  change d * A.card ≤ (L - 1) + (d - 1) at ha
  change d * B.card ≤ (N - R) + (d - 1) at hb
  omega

/-- A crooked member omits at least one point of its whole physical residue
class.  Thus its actual aligned step is strictly below its density rank. -/
theorem actual_aligned_modulus_lt {N d : ℕ} {S : Finset ℤ} {a : ℤ} {k : ℝ}
    (hd : 0 < d) (hS : S ⊆ Ground N) (hbad : ¬ IsAP S)
    (hdense : (N : ℝ) < k * S.card) (halign : ∀ y ∈ S, (d : ℤ) ∣ y - a) :
    (d : ℝ) < k := by
  have hcpos : 0 < S.card := by
    by_contra hn
    have hz : S.card = 0 := by omega
    rw [hz, Nat.cast_zero, mul_zero] at hdense
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    linarith only [hdense, hN0]
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hcpos
  let C := ResidueInterval 1 (N : ℤ) d a
  have hSC : S ⊆ C := by
    intro y hy
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ((mem_ground N y).mp (hS hy)), halign y hy⟩
  have hCAP : APAt (d : ℤ) a C := by
    refine ⟨by exact_mod_cast hd, 1, N, ?_⟩
    intro y
    simp only [C, ResidueInterval, Finset.mem_filter, Finset.mem_Icc]
    tauto
  have hCisAP : IsAP C := (isAP_iff_exists_APAt C).mpr
    ⟨d, x, apAt_rebase hCAP (hSC hx), hSC hx⟩
  have hstrict : S ⊂ C := Finset.ssubset_iff_subset_ne.mpr
    ⟨hSC, fun he => hbad (he ▸ hCisAP)⟩
  have hcard : (S.card : ℝ) + 1 ≤ C.card := by
    exact_mod_cast (show S.card + 1 ≤ C.card from Finset.card_lt_card hstrict)
  have hm := residue_interval_mass 1 (N : ℤ) a hd
  have hNc : ((N : ℤ) - 1 + 1).toNat = N := by omega
  rw [hNc] at hm
  have hd1 : 1 ≤ d := by omega
  have hmR : (d : ℝ) * C.card ≤ (N : ℝ) + ((d - 1 : ℕ) : ℝ) := by
    exact_mod_cast hm
  rw [Nat.cast_sub hd1, Nat.cast_one] at hmR
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hc := mul_le_mul_of_nonneg_left hcard hdR.le
  by_contra hn
  have hk : k ≤ (d : ℝ) := le_of_not_gt hn
  have hs := mul_le_mul_of_nonneg_right hk (Nat.cast_nonneg S.card : (0 : ℝ) ≤ S.card)
  nlinarith only [hmR, hc, hdense, hs]

/-- The exact two-arm constant is retained, including its negative part at
step one.  All terms count the same actual interval complement. -/
theorem actual_count_affine {N L R : ℕ} {E : Finset (Finset ℤ)}
    (D : Finset ℕ) (p q : ℕ → ℕ) (K : Finset ℤ → Key)
    (hL : 1 ≤ L) (hLR : L ≤ R) (hRN : R ≤ N)
    (hlegal : Legal (Ground N) E) (hbad : ∀ S ∈ E, ¬ IsAP S)
    (hD : ∀ d ∈ D, 0 < d) (hkeys : ∀ S ∈ E, K S ∈ Keys D p)
    (hanchor : ∀ S ∈ E, HasAnchor q (L : ℤ) (R : ℤ) (K S) S)
    (halign : ∀ S ∈ E, Aligned K q (L : ℤ) S) :
    (E.card : ℝ) ≤ ∑ d ∈ D, (((p d - 1) / d : ℕ) : ℝ) *
      (((L : ℝ) + (N : ℝ) - R) / d + 2 - 3 / d) := by
  obtain ⟨phase, hc⟩ := actual_count_from_anchors D p q K hlegal hbad hD hkeys hanchor halign
  have hcR : (E.card : ℝ) ≤ ∑ d ∈ D, (((p d - 1) / d : ℕ) : ℝ) *
      ((ResidueOutside N (L : ℤ) (R : ℤ) d (phase d)).card : ℝ) := by exact_mod_cast hc
  refine hcR.trans (Finset.sum_le_sum ?_)
  intro d hd
  have hd0 : 0 < d := hD d hd
  have hd1 : 1 ≤ d := by omega
  have hm := residue_outside_mass hL hLR hRN hd0 (phase d)
  have hmR : (d : ℝ) * (ResidueOutside N (L : ℤ) (R : ℤ) d (phase d)).card ≤
      ((L - 1 : ℕ) : ℝ) + ((N - R : ℕ) : ℝ) + 2 * ((d - 1 : ℕ) : ℝ) := by
    exact_mod_cast hm
  rw [Nat.cast_sub hL, Nat.cast_sub hRN, Nat.cast_sub hd1, Nat.cast_one] at hmR
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
  have hb : ((ResidueOutside N (L : ℤ) (R : ℤ) d (phase d)).card : ℝ) ≤
      ((L : ℝ) + N - R) / d + 2 - 3 / d := by
    have he : ((L : ℝ) + N - R) / d + 2 - 3 / d =
        ((L : ℝ) + N - R + 2 * d - 3) / d := by
      field_simp
    rw [he]
    apply (le_div_iff₀ hdR).mpr
    nlinarith only [hmR]
  exact mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _)

theorem grid_anchor_cover (M a b d m p q : ℕ)
    (ha : 1 ≤ a) (hb : b ≤ M) (hd : 0 < d) (hq : 0 < q)
    (hspan : b = a + d * (m - 1)) (hqm : q ≤ m - 1) (hMq : M ≤ p * q) :
    ∃ rho j : ℕ, (1 ≤ rho ∧ rho ≤ d) ∧ (1 ≤ j ∧ j ≤ (p - 1) / d) ∧
      (a : ℤ) ≤ (rho : ℤ) + ((j : ℤ) * q - 1) * d ∧
      (rho : ℤ) + ((j : ℤ) * q - 1) * d + d ≤ b ∧
      (d : ℤ) ∣ ((rho : ℤ) + ((j : ℤ) * q - 1) * d) - a := by
  let rho := (a - 1) % d + 1
  let z := (a - 1) / d
  let j := z / q + 1
  have hr : 1 ≤ rho ∧ rho ≤ d := by
    have hh := Nat.mod_lt (a - 1) hd
    dsimp only [rho]
    omega
  have haz : a = rho + d * z := by
    have hh := Nat.mod_add_div (a - 1) d
    dsimp only [rho, z]
    omega
  have hj : z < j * q ∧ j * q ≤ z + q := by
    have hh := Nat.mod_add_div z q
    have hl := Nat.mod_lt z hq
    dsimp only [j]
    constructor <;> nlinarith [Nat.zero_le (z % q)]
  let u := rho + j * q * d
  have hau : a + d ≤ u := by dsimp only [u]; nlinarith only [haz, hj.1]
  have hub : u ≤ b := by dsimp only [u]; nlinarith only [haz, hj.2, hspan, hqm]
  have hjd : j * d ≤ p - 1 := by
    by_contra hn
    have hpjd : p ≤ j * d := by omega
    have hh := Nat.mul_le_mul_left q hpjd
    dsimp only [u] at hub
    nlinarith only [hh, hub, hb, hMq, hr.1]
  have hjlo : 1 ≤ j := Nat.le_add_left 1 (z / q)
  have hjhi : j ≤ (p - 1) / d := (Nat.le_div_iff_mul_le hd).mpr hjd
  have hpoint : (rho : ℤ) + ((j : ℤ) * q - 1) * d = (u : ℤ) - d := by
    dsimp only [u]
    push_cast
    ring
  refine ⟨rho, j, hr, ⟨hjlo, hjhi⟩, ?_, ?_, ?_⟩
  · rw [hpoint]
    have hh : (a : ℤ) + d ≤ u := by exact_mod_cast hau
    omega
  · rw [hpoint]
    omega
  · rw [hpoint]
    refine ⟨((j * q : ℕ) : ℤ) - z - 1, ?_⟩
    have haZ : (a : ℤ) = rho + (d : ℤ) * z := by exact_mod_cast haz
    dsimp only [u]
    push_cast
    nlinarith only [haZ]

/-- Construct the actual two adjacent anchors for a supplied physical step.
Only its own quantum and its own trace length are used. -/
theorem actual_trace_anchor {S : Finset ℤ} {L R d : ℕ} {a : ℤ}
    (D : Finset ℕ) (p q : ℕ → ℕ)
    (hL : 1 ≤ L) (hLR : L ≤ R) (hdD : d ∈ D)
    (hAP : APAt (d : ℤ) a (S ∩ Finset.Icc (L : ℤ) (R : ℤ)))
    (hq : 0 < q d) (hMq : R - L + 1 ≤ p d * q d)
    (hqm : q d ≤ (S ∩ Finset.Icc (L : ℤ) (R : ℤ)).card - 1) :
    ∃ k ∈ Keys D p, k.1 = d ∧ HasAnchor q (L : ℤ) (R : ℤ) k S := by
  have hd : 0 < d := by exact_mod_cast hAP.1
  have hne : (S ∩ Finset.Icc (L : ℤ) (R : ℤ)).Nonempty :=
    Finset.card_pos.mp (by omega)
  let x := (S ∩ Finset.Icc (L : ℤ) (R : ℤ)).min' hne
  let y := (S ∩ Finset.Icc (L : ℤ) (R : ℤ)).max' hne
  have hxS : x ∈ S ∩ Finset.Icc (L : ℤ) (R : ℤ) := Finset.min'_mem _ hne
  have hyS : y ∈ S ∩ Finset.Icc (L : ℤ) (R : ℤ) := Finset.max'_mem _ hne
  have hxK := Finset.mem_Icc.mp (Finset.mem_inter.mp hxS).2
  have hyK := Finset.mem_Icc.mp (Finset.mem_inter.mp hyS).2
  have hxCast : (x.toNat : ℤ) = x := Int.toNat_of_nonneg (by omega)
  have hyCast : (y.toNat : ℤ) = y := Int.toNat_of_nonneg (by omega)
  have hspan := apAt_span_eq hAP hne
  have hspanN : y.toNat = x.toNat + d * ((S ∩ Finset.Icc (L : ℤ) (R : ℤ)).card - 1) := by
    have hh : (y.toNat : ℤ) = x.toNat + (d : ℤ) *
        (((S ∩ Finset.Icc (L : ℤ) (R : ℤ)).card - 1 : ℕ) : ℤ) := by
      rw [hxCast, hyCast, Nat.cast_sub (by omega : 1 ≤ (S ∩ Finset.Icc (L : ℤ) (R : ℤ)).card),
        Nat.cast_one]
      dsimp only [x, y]
      linarith only [hspan]
    exact_mod_cast hh
  have hspan' : y.toNat - L + 1 = (x.toNat - L + 1) +
      d * ((S ∩ Finset.Icc (L : ℤ) (R : ℤ)).card - 1) := by omega
  obtain ⟨rho, j, hr, hj, hau, hub, hdiv⟩ := grid_anchor_cover (R - L + 1)
    (x.toNat - L + 1) (y.toNat - L + 1) d
    (S ∩ Finset.Icc (L : ℤ) (R : ℤ)).card (p d) (q d)
    (by omega) (by omega) hd hq hspan' hqm hMq
  let k : Key := ⟨d, rho, j⟩
  have hk : k ∈ Keys D p := Finset.mem_sigma.mpr
    ⟨hdD, Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr hr, Finset.mem_Icc.mpr hj⟩⟩
  have hxShift : ((x.toNat - L + 1 : ℕ) : ℤ) = x - L + 1 := by omega
  have hyShift : ((y.toNat - L + 1 : ℕ) : ℤ) = y - L + 1 := by omega
  rw [hxShift] at hau hdiv
  rw [hyShift] at hub
  have hau' : x ≤ Origin q (L : ℤ) k := by dsimp only [Origin, k]; linarith only [hau]
  have hub' : Origin q (L : ℤ) k + d ≤ y := by dsimp only [Origin, k]; linarith only [hub]
  have hdiv' : (d : ℤ) ∣ Origin q (L : ℤ) k - x := by
    have he : Origin q (L : ℤ) k - x =
        ((rho : ℤ) + ((j : ℤ) * q d - 1) * d) - (x - L + 1) := by
      dsimp only [Origin, k]
      ring
    rw [he]
    exact hdiv
  have huS : Origin q (L : ℤ) k ∈ S ∩ Finset.Icc (L : ℤ) (R : ℤ) :=
    apAt_fill hAP hxS hyS hau' (by linarith only [hub', hAP.1]) hdiv'
  have hvS : Origin q (L : ℤ) k + d ∈ S ∩ Finset.Icc (L : ℤ) (R : ℤ) :=
    apAt_fill hAP hxS hyS (by linarith only [hau', hAP.1]) hub' (by
      rw [show Origin q (L : ℤ) k + d - x = (Origin q (L : ℤ) k - x) + d by ring]
      exact dvd_add hdiv' (dvd_refl _))
  exact ⟨k, hk, rfl, apAt_rebase hAP huS, huS, hvS⟩

def Quantum (M p : ℕ) : ℕ := (M + p - 1) / p

theorem quantum_geometry {M p : ℕ} (hM : 0 < M) (hp : 0 < p) :
    0 < Quantum M p ∧ M ≤ p * Quantum M p ∧ Quantum M p ≤ M / p + 1 := by
  have hpos : 0 < Quantum M p :=
    Nat.div_pos (by omega : p ≤ M + p - 1) hp
  have hrem := Nat.mod_lt (M + p - 1) hp
  have hdiv := Nat.mod_add_div (M + p - 1) p
  have hcover : M ≤ p * Quantum M p := by
    dsimp only [Quantum]
    omega
  have hupper := Nat.div_le_div_right (c := p) (show M + p - 1 ≤ M + p by omega)
  rw [Nat.add_div_right M hp] at hupper
  exact ⟨hpos, hcover, hupper⟩

theorem quantum_trace_bound {M p m : ℕ} (hM : 0 < M) (hp : 0 < p)
    (hm : (M : ℝ) / p + 1 < m) : Quantum M p ≤ m - 1 := by
  have hfloor : ((M / p : ℕ) : ℝ) ≤ (M : ℝ) / p := Nat.cast_div_le
  have hreal : ((M / p : ℕ) : ℝ) + 1 < m := by linarith only [hfloor, hm]
  have hnat : M / p + 1 < m := by exact_mod_cast hreal
  have hupper := (quantum_geometry hM hp).2.2
  omega

theorem actual_count_from_traces {N L R : ℕ} {E : Finset (Finset ℤ)}
    (D : Finset ℕ) (p q : ℕ → ℕ) (d : Finset ℤ → ℕ) (a : Finset ℤ → ℤ)
    (hL : 1 ≤ L) (hLR : L ≤ R) (hRN : R ≤ N)
    (hlegal : Legal (Ground N) E) (hbad : ∀ S ∈ E, ¬ IsAP S)
    (hD : ∀ e ∈ D, 0 < e) (hsteps : ∀ S ∈ E, d S ∈ D)
    (htrace : ∀ S ∈ E, APAt (d S : ℤ) (a S) (S ∩ Finset.Icc (L : ℤ) (R : ℤ)))
    (halign : ∀ S ∈ E, ∀ y ∈ S, (d S : ℤ) ∣ y - a S)
    (hq : ∀ e ∈ D, 0 < q e) (hMq : ∀ e ∈ D, R - L + 1 ≤ p e * q e)
    (hqm : ∀ S ∈ E, q (d S) ≤ (S ∩ Finset.Icc (L : ℤ) (R : ℤ)).card - 1) :
    (E.card : ℝ) ≤ ∑ e ∈ D, (((p e - 1) / e : ℕ) : ℝ) *
      (((L : ℝ) + (N : ℝ) - R) / e + 2 - 3 / e) := by
  have hcover : ∀ S ∈ E, ∃ k ∈ Keys D p,
      k.1 = d S ∧ HasAnchor q (L : ℤ) (R : ℤ) k S := by
    intro S hS
    exact actual_trace_anchor D p q hL hLR (hsteps S hS) (htrace S hS)
      (hq _ (hsteps S hS)) (hMq _ (hsteps S hS)) (hqm S hS)
  let K : Finset ℤ → Key := fun S =>
    if hS : S ∈ E then (hcover S hS).choose else ⟨1, 1, 1⟩
  have hK : ∀ S ∈ E, K S ∈ Keys D p ∧ (K S).1 = d S ∧
      HasAnchor q (L : ℤ) (R : ℤ) (K S) S := by
    intro S hS
    dsimp only [K]
    rw [dif_pos hS]
    exact (hcover S hS).choose_spec
  apply actual_count_affine D p q K hL hLR hRN hlegal hbad hD
    (fun S hS => (hK S hS).1) (fun S hS => (hK S hS).2.2)
  intro S hS y hy
  have hu := (Finset.mem_inter.mp (hK S hS).2.2.2.1).1
  change ((K S).1 : ℤ) ∣ y - Origin q (L : ℤ) (K S)
  rw [(hK S hS).2.1]
  rw [show y - Origin q (L : ℤ) (K S) =
    (y - a S) - (Origin q (L : ℤ) (K S) - a S) by ring]
  exact dvd_sub (halign S hS y hy) (halign S hS _ hu)

theorem residue_outside_real {N L R d : ℕ}
    (hL : 1 ≤ L) (hLR : L ≤ R) (hRN : R ≤ N) (hd : 0 < d) (a : ℤ) :
    ((ResidueOutside N (L : ℤ) (R : ℤ) d a).card : ℝ) ≤
      ((L : ℝ) + (N : ℝ) - R) / d + 2 - 3 / d := by
  have hd1 : 1 ≤ d := by omega
  have hm := residue_outside_mass hL hLR hRN hd a
  have hmR : (d : ℝ) * (ResidueOutside N (L : ℤ) (R : ℤ) d a).card ≤
      ((L - 1 : ℕ) : ℝ) + ((N - R : ℕ) : ℝ) + 2 * ((d - 1 : ℕ) : ℝ) := by
    exact_mod_cast hm
  rw [Nat.cast_sub hL, Nat.cast_sub hRN, Nat.cast_sub hd1, Nat.cast_one] at hmR
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have he : ((L : ℝ) + N - R) / d + 2 - 3 / d =
      ((L : ℝ) + N - R + 2 * d - 3) / d := by field_simp
  rw [he]
  apply (le_div_iff₀ hdR).mpr
  nlinarith only [hmR]

/-- The aligned trace loses only the actual residue capacity of its two
outside arms; the off-residue family is absent from this theorem. -/
theorem actual_aligned_trace_lower {N L R d : ℕ} {S : Finset ℤ} {a : ℤ} {k : ℝ}
    (hL : 1 ≤ L) (hLR : L ≤ R) (hRN : R ≤ N) (hd : 0 < d) (hk : 0 < k)
    (hS : S ⊆ Ground N) (hdense : (N : ℝ) < k * S.card)
    (halign : ∀ y ∈ S, (d : ℤ) ∣ y - a) :
    (N : ℝ) / k - ((L : ℝ) + (N : ℝ) - R) / d - 2 + 3 / d <
      ((S ∩ Finset.Icc (L : ℤ) (R : ℤ)).card : ℝ) := by
  have hsub : S \ Finset.Icc (L : ℤ) (R : ℤ) ⊆ ResidueOutside N (L : ℤ) (R : ℤ) d a := by
    intro y hy
    obtain ⟨hyS, hyI⟩ := Finset.mem_sdiff.mp hy
    exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hS hyS, hyI⟩, halign y hyS⟩
  have ho : ((S \ Finset.Icc (L : ℤ) (R : ℤ)).card : ℝ) ≤
      (ResidueOutside N (L : ℤ) (R : ℤ) d a).card := by
    exact_mod_cast Finset.card_le_card hsub
  have hc := Finset.card_sdiff_add_card_inter S (Finset.Icc (L : ℤ) (R : ℤ))
  have hcR : ((S \ Finset.Icc (L : ℤ) (R : ℤ)).card : ℝ) +
      (S ∩ Finset.Icc (L : ℤ) (R : ℤ)).card = S.card := by exact_mod_cast hc
  have hm := residue_outside_real hL hLR hRN hd a
  have hsize : (N : ℝ) / k < S.card :=
    (div_lt_iff₀ hk).mpr (by simpa only [mul_comm] using hdense)
  linarith only [ho, hcR, hm, hsize]

theorem aligned_trace_gate_real {n w k u p d t : ℝ}
    (hd : 0 < d) (hdp : d < p) (hwidth : w < n / u)
    (htrace : n / k - w / d - 2 + 3 / d < t)
    (hgate : 3 - 3 / d + 1 / p < n *
      (1 / k - 1 / p - (1 / d - 1 / p) / u)) :
    (n + 1 - w) / p + 1 < t := by
  have hcoef : 0 < 1 / d - 1 / p :=
    sub_pos.mpr (one_div_lt_one_div_of_lt hd hdp)
  have hwidthpay := mul_pos hcoef (sub_pos.mpr hwidth)
  have hid : (n / k - w / d - 2 + 3 / d) - ((n + 1 - w) / p + 1) =
      (n * (1 / k - 1 / p - (1 / d - 1 / p) / u) - (3 - 3 / d + 1 / p)) +
        (1 / d - 1 / p) * (n / u - w) := by ring
  linarith only [htrace, hgate, hwidthpay, hid]

/-- The public gate-to-count bridge uses the supplied actual traces and
their actual physical step, on the same original ground and central interval. -/
theorem actual_count_from_gates {N L R : ℕ} {E : Finset (Finset ℤ)} {k u : ℝ}
    (D : Finset ℕ) (p : ℕ → ℕ) (d : Finset ℤ → ℕ) (a : Finset ℤ → ℤ)
    (hL : 1 ≤ L) (hLR : L ≤ R) (hRN : R ≤ N) (hk : 0 < k)
    (hlegal : Legal (Ground N) E) (hbad : ∀ S ∈ E, ¬ IsAP S)
    (hD : ∀ e ∈ D, 0 < e) (hp : ∀ e ∈ D, e < p e)
    (hsteps : ∀ S ∈ E, d S ∈ D)
    (htrace : ∀ S ∈ E, APAt (d S : ℤ) (a S) (S ∩ Finset.Icc (L : ℤ) (R : ℤ)))
    (halign : ∀ S ∈ E, ∀ y ∈ S, (d S : ℤ) ∣ y - a S)
    (hdense : ∀ S ∈ E, (N : ℝ) < k * S.card)
    (hwidth : (L : ℝ) + (N : ℝ) - R < (N : ℝ) / u)
    (hgate : ∀ e ∈ D, 3 - 3 / (e : ℝ) + 1 / (p e : ℝ) < (N : ℝ) *
      (1 / k - 1 / (p e : ℝ) - (1 / (e : ℝ) - 1 / (p e : ℝ)) / u)) :
    (E.card : ℝ) ≤ ∑ e ∈ D, (((p e - 1) / e : ℕ) : ℝ) *
      (((L : ℝ) + (N : ℝ) - R) / e + 2 - 3 / e) := by
  let M := R - L + 1
  let q : ℕ → ℕ := fun e => Quantum M (p e)
  have hM : 0 < M := by dsimp only [M]; omega
  have hMR : (M : ℝ) = (N : ℝ) + 1 - ((L : ℝ) + (N : ℝ) - R) := by
    dsimp only [M]
    rw [Nat.cast_add, Nat.cast_sub hLR, Nat.cast_one]
    ring
  have hp0 : ∀ e ∈ D, 0 < p e := fun e he => lt_trans (hD e he) (hp e he)
  apply actual_count_from_traces D p q d a hL hLR hRN hlegal hbad hD hsteps htrace halign
    (fun e he => (quantum_geometry hM (hp0 e he)).1)
    (fun e he => (quantum_geometry hM (hp0 e he)).2.1)
  intro S hS
  have hstep := hsteps S hS
  have ht := actual_aligned_trace_lower hL hLR hRN (hD _ hstep) hk (hlegal.1 S hS)
    (hdense S hS) (halign S hS)
  have hdR : (0 : ℝ) < d S := by exact_mod_cast hD _ hstep
  have hdpR : (d S : ℝ) < p (d S) := by exact_mod_cast hp _ hstep
  have hm := aligned_trace_gate_real hdR hdpR hwidth ht (hgate _ hstep)
  rw [← hMR] at hm
  exact quantum_trace_bound hM (hp0 _ hstep) hm

#print axioms actual_private_point
#print axioms actual_step_common_residue
#print axioms actual_count_from_anchors
#print axioms residue_outside_mass
#print axioms actual_aligned_modulus_lt
#print axioms actual_count_affine
#print axioms grid_anchor_cover
#print axioms actual_trace_anchor
#print axioms quantum_geometry
#print axioms quantum_trace_bound
#print axioms actual_count_from_traces
#print axioms actual_aligned_trace_lower
#print axioms aligned_trace_gate_real
#print axioms actual_count_from_gates
end
end JSP233.Aligned208
