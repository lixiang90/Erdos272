module

public import Erdos272.Foundation.ProofTactics
public import Mathlib.Basic.Real.Basic

@[expose] public section

/-! The short-step supply inequalities use the *same* physical root `c`
as the profile. Each objective is affine in `c`. Thus both endpoint
quadratics may be completed before interpolating back to the actual root. -/
namespace JSP233.ShortSupplyProfile20258

noncomputable section
set_option autoImplicit false

def alpha : ℝ := 23359/80000
def kappa : ℝ := 129/200
def price : ℝ := 24487/2000

def profile (L b c : ℝ) : ℝ := alpha*L^2-kappa*c*b+b^2/2-50*L+c

/-- A square certificate for a quadratic with the mixed term `-k*L*b`. -/
private theorem quadratic_bound {L b k u v E : ℝ} (hD : 0 < 2*alpha-k^2)
    (hE : (u+k*v)^2+(2*alpha-k^2)*v^2 ≤ 2*(2*alpha-k^2)*E) :
    -E ≤ alpha*L^2-k*L*b+b^2/2-u*L-v*b := by
  have h : 0 ≤ 2*(2*alpha-k^2)*(alpha*L^2-k*L*b+b^2/2-u*L-v*b+E) := by
    calc
      0 ≤ ((2*alpha-k^2)*L-(u+k*v))^2 +
          (2*alpha-k^2)*(b-k*L-v)^2 +
          (2*(2*alpha-k^2)*E-((u+k*v)^2+(2*alpha-k^2)*v^2)) :=
        add_nonneg (add_nonneg (sq_nonneg _) (mul_nonneg hD.le (sq_nonneg _))) (sub_nonneg.mpr hE)
      _ = _ := by ring
  have hh := nonneg_of_mul_nonneg_right h (show 0 < 2*(2*alpha-k^2) by linarith only [hD])
  linarith only [hh]

structure Objective where
  a : ℝ
  cWeight : ℝ
  bWeight : ℝ
  target : ℝ
  multiplier : ℝ

private structure Estimate where
  start : ℝ
  rate : ℝ
  left : ℝ
  right : ℝ
  root : ℝ
  offset : ℝ

private def sharp : Estimate := ⟨11400,price,50,0,1,884⟩
private def coarse : Estimate := ⟨19227,17,75,15,0,872⟩

private def Estimate.value (e : Estimate) (L b c : ℝ) :=
  alpha*L^2-kappa*c*b+b^2/2-e.left*L-e.right*b+e.root*c

private def Estimate.margin (e : Estimate) (o : Objective) :=
  (o.multiplier*o.target-e.rate)*e.start-e.offset

private def Estimate.valid (e : Estimate) (o : Objective) : Prop :=
  let v := e.right+o.multiplier*o.bWeight
  0 < o.multiplier ∧ 0 ≤ o.multiplier*o.target-e.rate ∧
  (e.left+o.multiplier*o.a)^2+(2*alpha)*v^2 ≤ 2*(2*alpha)*e.margin o ∧
  (e.left-e.root+o.multiplier*(o.a+o.cWeight)+kappa*v)^2+
    (2*alpha-kappa^2)*v^2 ≤ 2*(2*alpha-kappa^2)*e.margin o

def margin (o : Objective) : ℝ := (o.multiplier*o.target-price)*11400-884

def Valid (o : Objective) : Prop :=
  0 < o.multiplier ∧ 0 ≤ o.multiplier*o.target-price ∧
  (50+o.multiplier*o.a)^2+(2*alpha)*(o.multiplier*o.bWeight)^2 ≤ 2*(2*alpha)*margin o ∧
  (49+o.multiplier*(o.a+o.cWeight)+kappa*(o.multiplier*o.bWeight))^2+
    (2*alpha-kappa^2)*(o.multiplier*o.bWeight)^2 ≤ 2*(2*alpha-kappa^2)*margin o

private theorem linear_bound (e : Estimate) (o : Objective) (ho : e.valid o) {N L b c : ℝ}
    (hn : e.start ≤ N) (hc : 0 ≤ c) (hcL : c ≤ L) (hp : e.value L b c ≤ e.rate*N+e.offset) :
    o.a*L+o.cWeight*c+o.bWeight*b ≤ o.target*N := by
  obtain ⟨hl,hs,h0,h1⟩ := ho
  have z := quadratic_bound (L := L) (b := b) (k := 0) (u := e.left+o.multiplier*o.a)
    (v := e.right+o.multiplier*o.bWeight) (E := e.margin o)
    (by norm_num [alpha]) (by simpa using h0)
  have endp := quadratic_bound (L := L) (b := b) (k := kappa)
    (u := e.left-e.root+o.multiplier*(o.a+o.cWeight))
    (v := e.right+o.multiplier*o.bWeight) (E := e.margin o) (by norm_num [alpha,kappa]) h1
  have lower : -(e.margin o) ≤ e.value L b c-o.multiplier*(o.a*L+o.cWeight*c+o.bWeight*b) := by
    unfold Estimate.value
    by_cases h : 0 ≤ e.root-kappa*b-o.multiplier*o.cWeight
    · nlinarith only [z,mul_nonneg hc h]
    · nlinarith only [endp,mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hcL) (le_of_not_ge h)]
  apply (le_of_mul_le_mul_left _ hl)
  have ht := mul_nonneg hs (sub_nonneg.mpr hn)
  unfold Estimate.margin at lower
  nlinarith only [hp,lower,ht]

/-- Prefix, long-step and width inequalities, with subtractions moved to
the other side so that the conclusions also make sense over naturals. -/
structure Gates (N c L b : ℕ) : Prop where
  prefixLow : 105*(2002*L+1193*b) ≤ 19159*N+105*1810*c
  prefixMid : 30*L+19*b ≤ 3*N+26*c
  prefixHigh : 12*L+4*b ≤ N+11*c
  longLow : 210*(1001*L+192*c+192*b) ≤ 39319*N
  longMid : 2*(15*L+4*c+4*b) ≤ 7*N
  longHigh : 6*L+b ≤ N+2*c
  wide : 2*L+b ≤ N+c

private def prefixLow : Objective := ⟨2002,-1810,1193,19159/105,9/50⟩
private def prefixMid : Objective := ⟨30,-26,19,3,11⟩
private def prefixHigh : Objective := ⟨12,-11,4,1,29⟩
private def longLow : Objective := ⟨1001,192,192,39319/210,173/1000⟩
private def longMid : Objective := ⟨15,4,4,7/2,9⟩
private def longHigh : Objective := ⟨6,-2,1,1,35⟩
private def wide : Objective := ⟨2,-1,1,1,54⟩

private def objectives := [prefixLow,prefixMid,prefixHigh,longLow,longMid,longHigh,wide]

private theorem of_estimate (e : Estimate) {N c L b : ℕ} (hn : e.start ≤ N) (hc : c ≤ L)
    (hp : e.value L b c ≤ e.rate*N+e.offset) (checked : ∀ o ∈ objectives, e.valid o) :
    Gates N c L b := by
  have bound (o : Objective) (h : o ∈ objectives) := linear_bound e o (checked o h)
    hn (Nat.cast_nonneg c)
    (show (c : ℝ) ≤ L by exact_mod_cast hc) hp
  constructor
  · have h := bound prefixLow (by simp [objectives])
    dsimp only [prefixLow] at h
    exact_mod_cast (show (105 : ℝ)*(2002*L+1193*b) ≤ 19159*N+105*1810*c by linarith only [h])
  · have h := bound prefixMid (by simp [objectives])
    dsimp only [prefixMid] at h
    exact_mod_cast (show (30 : ℝ)*L+19*b ≤ 3*N+26*c by linarith only [h])
  · have h := bound prefixHigh (by simp [objectives])
    dsimp only [prefixHigh] at h
    exact_mod_cast (show (12 : ℝ)*L+4*b ≤ N+11*c by linarith only [h])
  · have h := bound longLow (by simp [objectives])
    dsimp only [longLow] at h
    exact_mod_cast (show (210 : ℝ)*(1001*L+192*c+192*b) ≤ 39319*N by linarith only [h])
  · have h := bound longMid (by simp [objectives])
    dsimp only [longMid] at h
    exact_mod_cast (show (2 : ℝ)*(15*L+4*c+4*b) ≤ 7*N by linarith only [h])
  · have h := bound longHigh (by simp [objectives])
    dsimp only [longHigh] at h
    exact_mod_cast (show (6 : ℝ)*L+b ≤ N+2*c by linarith only [h])
  · have h := bound wide (by simp [objectives])
    dsimp only [wide] at h
    exact_mod_cast (show (2 : ℝ)*L+b ≤ N+c by linarith only [h])

private theorem checked (e : Estimate) (which : e=sharp ∨ e=coarse) :
    ∀ o ∈ objectives, e.valid o := by
  intro o ho
  simp only [objectives,List.mem_cons,List.not_mem_nil,or_false] at ho
  rcases ho with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rcases which with rfl|rfl <;>
    norm_num [Estimate.valid,Estimate.margin,sharp,coarse,prefixLow,prefixMid,prefixHigh,
      longLow,longMid,longHigh,wide,alpha,kappa,price]

theorem of_profile {N c L b : ℕ} (hn : 11400 ≤ N) (hc : c ≤ L)
    (hp : profile L b c ≤ price*N+884) : Gates N c L b :=
  of_estimate sharp (by dsimp [sharp]; exact_mod_cast hn) hc
    (by simpa only [sharp,Estimate.value,zero_mul,sub_zero,one_mul,profile] using hp)
    (checked sharp (Or.inl rfl))

theorem of_rooted_exterior {N c L b : ℕ} (hn : 19227 ≤ N) (hc : c ≤ L)
    (hp : alpha*(L : ℝ)^2-kappa*c*b+(b : ℝ)^2/2 ≤ 17*N+75*L+15*b+872) :
    Gates N c L b := by
  apply of_estimate coarse (by dsimp [coarse]; exact_mod_cast hn) hc _ (checked coarse (Or.inr rfl))
  dsimp only [coarse,Estimate.value]
  linarith only [hp]

#print axioms of_rooted_exterior

end
end JSP233.ShortSupplyProfile20258
