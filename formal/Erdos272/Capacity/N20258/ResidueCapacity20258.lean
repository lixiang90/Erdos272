module

public import Erdos272.Counting.N20258.CubicSieve20258
public import Erdos272.Geometry.N20258.PhaseCells20258
public import Erdos272.Capacity.N88404.SieveCapacity88404

@[expose] public section
namespace JSP233.ResidueCapacity20258
open StarCompletion APGeometry APShadowCapacity16858 IntrinsicTriples208
open APClasses88404 APClassFrame88404 AffineLine30 AffineShadow94488
open OrderedShadow88404 PhaseCard88404 InclusionExclusion88404
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false

def steps : Finset ℕ := PairError20258.steps.toFinset
def later (d : ℕ) : List ℕ := PairError20258.primes.filter (fun p => d < p)
def beta (d : ℕ) : ℚ := CubicSieve20258.coefficient (later d) 3

theorem positive {d : ℕ} (hd : d ∈ steps) : 0 < d :=
  (by decide +kernel : ∀ p ∈ PairError20258.steps, 0 < p) d (List.mem_toFinset.mp hd)

private theorem coprime {d p : ℕ} (hd : d ∈ steps) (hp : p ∈ steps) (h : d ≠ p) :
    Nat.Coprime d p :=
  (by decide +kernel : ∀ i ∈ PairError20258.steps, ∀ j ∈ PairError20258.steps,
    i ≠ j → Nat.Coprime i j) d (List.mem_toFinset.mp hd) p (List.mem_toFinset.mp hp) h

private theorem later_mem {p d : ℕ} (hp : p ∈ (later d).toFinset) : p ∈ steps ∧ d < p := by
  obtain ⟨h,hl⟩ := List.mem_filter.mp (List.mem_toFinset.mp hp)
  exact ⟨List.mem_toFinset.mpr (List.mem_cons_of_mem 1 h), by simpa using hl⟩

private theorem mem_later {p d : ℕ} (hp : p ∈ steps) (hd : d ∈ steps) (h : d < p) :
    p ∈ (later d).toFinset := by
  have hp' : p ∈ 1::PairError20258.primes := List.mem_toFinset.mp hp
  rcases List.mem_cons.mp hp' with h1 | hP
  · have := positive hd
    omega
  · exact List.mem_toFinset.mpr (List.mem_filter.mpr ⟨hP, by simpa using h⟩)

private theorem factor_product (K : Finset ℕ) (k : ℕ) :
    CubicSieve20258.factor (fun j => (1 : ℚ)/(j : ℚ)^k) K =
      1/((∏ j ∈ K, j : ℕ) : ℚ)^k := by
  induction K using Finset.induction_on with
  | empty => simp [CubicSieve20258.factor]
  | @insert a K ha ih =>
    unfold CubicSieve20258.factor at ih ⊢
    rw [Finset.prod_insert ha, Finset.prod_insert ha, ih, Nat.cast_mul, mul_pow]
    simp [one_div, mul_comm]

private theorem frame_bound {N d : ℕ} {U : Finset (Finset ℤ)}
    (hd : d ∈ steps) (f : Frame N d U) (r : ℕ → ℤ) :
    beta d * (APShadow U).card - PairError20258.weight d * (f.size : ℚ)^2 ≤
      (Avoid (APShadow U) (fun j => AllPhase j (r j)) (later d).toFinset).card := by
  let T := APShadow f.family
  have hpos := positive hd
  have hdZ : (0 : ℤ) < d := by exact_mod_cast hpos
  have he : APShadow U = T.image (mapSet f.offset (d : ℤ)) :=
    (congrArg APShadow f.mapped).symm.trans (map_shadow f.offset (d : ℤ) hdZ f.family)
  have hc : (APShadow U).card = T.card := by
    rw [he]
    exact Finset.card_image_of_injective _ (mapSet_injective f.offset (d : ℤ) hdZ)
  let P := fun j => AllPhase j (r j)
  have hb (K : Finset ℕ) (hk : K ⊆ (later d).toFinset) :
      ((Intersect (APShadow U) P K).card : ℚ) ≤
        (APShadow U).card * CubicSieve20258.factor CubicSieve20258.density K ∧
      (APShadow U).card * CubicSieve20258.factor CubicSieve20258.density K -
        ((3/2 : ℚ)*(f.size : ℚ)^2) * CubicSieve20258.factor PairError20258.reciprocal K ≤
          (Intersect (APShadow U) P K).card := by
    have hkS : ∀ j ∈ K, j ∈ steps := fun j hj => (later_mem (hk hj)).1
    have hh := PhaseCells20258.intersection (shadow_carrier f.ground) (shadow_closed f.intervals)
      hpos K id (fun j hj => positive (hkS j hj))
      (fun i hi j hj hij => coprime (hkS i hi) (hkS j hj) hij)
      (fun j hj => coprime hd (hkS j hj) (ne_of_lt (later_mem (hk hj)).2)) f.offset r
    dsimp only [id_eq] at hh
    rw [hc, he]
    let I := Intersect (T.image (mapSet f.offset (d : ℤ))) P K
    let q : ℕ := ∏ j ∈ K, j
    rw [show CubicSieve20258.factor CubicSieve20258.density K = 1/(q : ℚ)^3 from
        factor_product K 3,
      show CubicSieve20258.factor PairError20258.reciprocal K = 1/(q : ℚ)^2 from
        factor_product K 2]
    change (I.card : ℚ) ≤ T.card * (1/(q : ℚ)^3) ∧
      T.card * (1/(q : ℚ)^3) - (3/2*(f.size : ℚ)^2) * (1/(q : ℚ)^2) ≤ I.card
    have upper : (I.card : ℚ) ≤ T.card/(q : ℚ)^3 := by
      apply (Rat.cast_le (K := ℝ)).mp
      push_cast
      exact hh.2
    have lower : (T.card : ℚ)/(q : ℚ)^3-3*(f.size : ℚ)^2/(2*(q : ℚ)^2) ≤ I.card := by
      apply (Rat.cast_le (K := ℝ)).mp
      push_cast
      exact hh.1
    simp only [div_eq_mul_inv, mul_inv_rev] at upper lower ⊢
    constructor <;> linarith only [upper, lower]
  have nd : (later d).Nodup := List.Nodup.filter _ (by decide +kernel : PairError20258.primes.Nodup)
  have h := CubicSieve20258.priced (APShadow U) P (later d) nd ((3/2)*(f.size : ℚ)^2)
    (fun K hk => (hb K hk).1) (fun K hk => (hb K hk).2)
  change CubicSieve20258.coefficient (later d) 3 * (APShadow U).card -
    (3/2*PairError20258.pairs (later d))*(f.size : ℚ)^2 ≤ _
  linarith only [h]

/-- The intrinsic triple pools of the original family and the shadows on all
nineteen strides fit in one ground-set capacity with a single quadratic fee. -/
theorem actual_capacity {N : ℕ} {F : Finset (Finset ℤ)} (hN : 1 ≤ N)
    (legal : Legal (Ground N) F) :
    (∑ S ∈ F, ((Pool S).card : ℚ)) +
      (∑ d ∈ steps, beta d*((APShadow (StepAP F d)).card : ℚ)) ≤
      (N.choose 3 : ℚ)+(99*((N : ℚ)-1)^2+210*((N : ℚ)-1)+120)/1000 := by
  let f : ∀ d ∈ steps, Frame N d (StepAP F d) :=
    fun d hd => Classical.choice (frame_nonempty hN (positive hd) legal)
  let r : ℕ → ℤ := fun d => if hd : d ∈ steps then (f d hd).offset else 0
  let S := fun d => APShadow (StepAP F d)
  let A := fun d => Avoid (S d) (fun j => AllPhase j (r j)) (later d).toFinset
  have phase : ∀ d ∈ steps, ∀ Q ∈ S d, AllPhase d (r d) Q := by
    intro d hd Q hQ
    simpa only [r, dite_eq_left hd] using SievePieces88404.frame_shadow_phase (positive hd) (f d hd) hQ
  have disj : Set.Pairwise (↑steps) (fun d p => Disjoint (A d) (A p)) := by
    intro d hd p hp hdp
    apply Finset.disjoint_left.mpr
    intro Q hD hP
    obtain ⟨hD,ad⟩ := Finset.mem_filter.mp hD
    obtain ⟨hP,ap⟩ := Finset.mem_filter.mp hP
    rcases lt_or_gt_of_ne hdp with h | h
    · exact ad p (mem_later hp hd h) (phase p hp Q hP)
    · exact ap d (mem_later hd hp h) (phase d hd Q hD)
  let U := steps.biUnion (StepAP F)
  have sub : steps.biUnion A ⊆ APShadow U := by
    rw [SieveCapacity88404.shadow_biUnion]
    intro Q hQ
    obtain ⟨d,hd,hD⟩ := Finset.mem_biUnion.mp hQ
    exact Finset.mem_biUnion.mpr ⟨d, hd, (Finset.mem_filter.mp hD).1⟩
  have shadow : (∑ d ∈ steps, ((A d).card : ℚ)) ≤ (APShadow U).card := by
    exact_mod_cast (Finset.card_biUnion disj ▸ Finset.card_le_card sub :
      ∑ d ∈ steps, (A d).card ≤ (APShadow U).card)
  have uf : U ⊆ F := by
    intro Q hQ
    obtain ⟨d,_,h⟩ := Finset.mem_biUnion.mp hQ
    exact APClasses88404.subset F d h
  have allAP : ∀ Q ∈ U, IsAP Q := by
    intro Q hQ
    obtain ⟨_,_,h⟩ := Finset.mem_biUnion.mp hQ
    exact APClasses88404.is_ap h
  have capacity := actual_AP_family_capacity legal uf allAP
  rw [ground_card] at capacity
  have capQ : (∑ S ∈ F, ((Pool S).card : ℚ))+(APShadow U).card ≤ (N.choose 3 : ℚ) := by
    exact_mod_cast capacity
  let n : ℚ := N-1
  have npos : 0 ≤ n := sub_nonneg.mpr (by exact_mod_cast hN)
  have each (d : ℕ) (hd : d ∈ steps) :
      beta d*(S d).card-PairError20258.weight d*(1+n/(d : ℚ))^2 ≤ (A d).card := by
    have dd : (0 : ℚ) < d := by exact_mod_cast positive hd
    have span : (d : ℚ)*(((f d hd).size : ℚ)-1) ≤ (N : ℚ)-1 := by
      exact_mod_cast (f d hd).span
    have ms : ((f d hd).size : ℚ) ≤ 1+n/d := by
      have h : ((f d hd).size : ℚ)-1 ≤ n/d :=
        (le_div_iff₀ dd).mpr (by linarith only [span])
      linarith only [h]
    have weight := (by decide +kernel : ∀ d ∈ PairError20258.steps, 0 ≤ PairError20258.weight d)
      d (List.mem_toFinset.mp hd)
    have fee := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) ms 2) weight
    have cost := frame_bound hd (f d hd) r
    change beta d*(S d).card-PairError20258.weight d*((f d hd).size : ℚ)^2 ≤ (A d).card at cost
    linarith only [cost,fee]
  have sum := Finset.sum_le_sum each
  rw [Finset.sum_sub_distrib] at sum
  have fees : (∑ d ∈ steps, PairError20258.weight d*(1+n/(d : ℚ))^2) = PairError20258.fee PairError20258.steps n :=
    List.sum_toFinset _ (by decide +kernel : PairError20258.steps.Nodup)
  rw [fees] at sum
  change _ + (∑ d ∈ steps, beta d*(S d).card) ≤ (N.choose 3 : ℚ)+(99*n^2+210*n+120)/1000
  linarith only [capQ,shadow,sum,PairError20258.uniform n npos]

#print axioms actual_capacity
end
end JSP233.ResidueCapacity20258
