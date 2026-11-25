module

public import Mathlib.Data.Nat.Basic

@[expose] public section
namespace JSP233.EndpointCover20258
set_option autoImplicit false

def rows (a : ℕ) : List ℕ → List (ℕ×ℕ)
  | [] => []
  | b::bs => (a,b)::rows (b+1) bs

def increasing (a z : ℕ) : List ℕ → Bool
  | [] => decide (z<a)
  | b::bs => decide (a≤b ∧ b≤z) && increasing (b+1) z bs

theorem locate {N a z : ℕ} (bs : List ℕ) (h : increasing a z bs=true)
    (lo : a≤N) (hi : N≤z) : ∃ p ∈ rows a bs, p.1≤N ∧ N≤p.2 ∧ p.2≤z := by
  induction bs generalizing a with
  | nil => simp [increasing] at h; omega
  | cons b bs ih =>
    simp only [increasing,Bool.and_eq_true,decide_eq_true_eq] at h
    by_cases inside : N≤b
    · exact ⟨(a,b),List.mem_cons_self,lo,inside,h.1.2⟩
    · obtain ⟨p,hp,hn⟩ := ih h.2 (by omega)
      exact ⟨p,List.mem_cons_of_mem _ hp,hn⟩

end JSP233.EndpointCover20258
