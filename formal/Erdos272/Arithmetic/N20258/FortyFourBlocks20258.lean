module

public import Erdos272.Counting.N20258.IntervalGapTails20258
public import Erdos272.Capacity.N20258.ResidueCapacity20258

@[expose] public section
namespace JSP233.FortyFourBlocks20258
open ResidueCapacity20258
open scoped BigOperators
set_option autoImplicit false

def target (a : ℕ) : ℕ := a*(a-1)/2+1+(a-1)/4
def cap (b : ℕ) : ℕ := 1893*b-84239

noncomputable def lowTail (b : ℕ) : ℕ :=
  StrideQuotients20258.compactTail (b-1) 43 143 steps

noncomputable def highTail (b : ℕ) : ℕ :=
  IntervalGapTails20258.grouped (b-1) 143 44 1877 43 steps

def price (b t c : ℕ) : ℚ :=
  let n : ℚ := ((b-1 : ℕ) : ℚ)
  let x := 5*n/6
  1+t+(362323/1000000*n^2+2834/1000*n+1)+(83*44*b)/x+(1-529/x)*c

def good (a b : ℕ) : Prop :=
  price b (lowTail b) (1877*(b-2)) ≤ target a ∧ price b (highTail b) (cap b) ≤ target a

private def rows : List (ℕ × ℕ) := [
  (20258,20259),(20260,20262),(20263,20266),(20267,20270),(20271,20275),
  (20276,20280),(20281,20285),(20286,20291),(20292,20298),(20299,20305),
  (20306,20313),(20314,20321),(20322,20330),(20331,20340),(20341,20351),
  (20352,20363),(20364,20376),(20377,20390),(20391,20406),(20407,20423),
  (20424,20442),(20443,20463),(20464,20485),(20486,20510),(20511,20537),
  (20538,20567),(20568,20600),(20601,20636),(20637,20675),(20676,20718),
  (20719,20765),(20766,20816),(20817,20872),(20873,20933),(20934,21000),
  (21001,21024),(21025,21100),(21101,21183),(21184,21274),(21275,21373),
  (21374,21481),(21482,21600)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 6000000 in
private theorem prices (j : ℕ) (hj : j<7) : ∀ r ∈ (rows.drop (6*j)).take 6, good r.1 r.2 := by
  unfold good
  interval_cases j <;> decide +kernel

private def adjacent (a b : ℕ) : List (ℕ × ℕ) → Bool
  | [] => decide (b<a)
  | (l,u)::rs => decide (l=a ∧ l≤u ∧ u≤b) && adjacent (u+1) b rs

private theorem locate {N b : ℕ} (rs : List (ℕ × ℕ)) {a : ℕ}
    (chain : adjacent a b rs=true) (lo : a≤N) (hi : N≤b) :
    ∃ r ∈ rs, r.1≤N ∧ N≤r.2 ∧ r.2≤b := by
  induction rs generalizing a with
  | nil => simp [adjacent] at chain; omega
  | cons r rs ih =>
    obtain ⟨l,u⟩ := r
    simp only [adjacent,Bool.and_eq_true,decide_eq_true_eq] at chain
    by_cases inside : N≤u
    · exact ⟨(l,u),List.mem_cons_self,chain.1.1 ▸ lo,inside,chain.1.2.2⟩
    · obtain ⟨s,hs,h⟩ := ih chain.2 (by omega)
      exact ⟨s,List.mem_cons_of_mem _ hs,h⟩

/-- Each integer is covered by a checked upper-ground pair of inequalities. -/
theorem cover {N : ℕ} (lo : 20258≤N) (hi : N≤21600) :
    ∃ a b : ℕ, a≤N ∧ N≤b ∧ b≤21600 ∧ good a b := by
  obtain ⟨r,hr,l,u,t⟩ := locate rows (by decide +kernel : adjacent 20258 21600 rows=true) lo hi
  have pieces : ∀ row ∈ rows, ∃ j ∈ Finset.range 7, row ∈ (rows.drop (6*j)).take 6 := by decide +kernel
  obtain ⟨j,hj,mem⟩ := pieces r hr
  exact ⟨r.1,r.2,l,u,t,prices j (Finset.mem_range.mp hj) r mem⟩

#print axioms cover
end JSP233.FortyFourBlocks20258
