module

public import OverfullWork.UniformFactorization

@[expose] public section


/-! # Arithmetic bridge from balanced integer loads to Hall budgets

This does not assume or assert existence of a weighted equitable colouring.
It turns an actually proved pairwise-load bound into its sharp integral
mean bound, for use with occupied weights in the original multigraph.
-/
namespace OverfullWork.Gate8J2C
open Finset

/-- Pairwise load spread L implies an occupied-load bound floor(total/q)+L.
The floor incurs no additional +1 error. -/
theorem load_le_floor_average_add {q : ℕ} (hq : 0<q) (load : Fin q → ℕ) (L : ℕ)
    (hspread : ∀ i j,load i≤load j+L) (i : Fin q) :
    load i≤(∑ j,load j)/q+L := by
  have hsum : q*load i≤(∑ j,load j)+q*L := by
    have hh:=sum_le_sum (s:=univ) (fun j _ => hspread i j)
    simpa only [sum_const,sum_add_distrib,card_univ,Fintype.card_fin,
      nsmul_eq_mul,Nat.cast_id] using hh
  by_contra hn
  have hlow : (∑ j,load j)/q+L+1≤load i:=by omega
  have hmul:=Nat.mul_le_mul_left q hlow
  have hfloor:=Nat.lt_mul_div_succ (∑ j,load j) hq
  nlinarith only [hsum,hmul,hfloor]

end OverfullWork.Gate8J2C
