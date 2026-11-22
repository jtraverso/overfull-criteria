module

public import OverfullWork.DirectedMultiplicityDemands
public import OverfullWork.DirectedMultigraphFactors

@[expose] public section


/-! The reduced multidigraph factorization in Osthus–Staden §5.1.
The robust support can belong to a separate submatrix of the reduced graph. -/
namespace OverfullWork.DirectedMultigraphFactors
open Finset DirectedRobustExpansion
open scoped Classical
variable {V : Type*} [Fintype V]

theorem exists_reduced_factorization (M C : V → V → ℕ) (D : Digraph V) (c k : ℕ)
    (ν τ α ε ρ : ℝ) (hν : 0 < ν) (hν1 : ν ≤ 1)
    (hντ : ν ≤ τ) (hτα : 4*τ ≤ α) (hε : 0 ≤ ε) (hεν : 16*ε ≤ ν)
    (hρ : 0 ≤ ρ) (hρν : 3*ρ ≤ (c:ℝ)*ν^2)
    (hOrder : 8 ≤ α*(Fintype.card V:ℝ))
    (hSub : ∀ v w, C v w ≤ M v w) (hCap : ∀ v w, D.Adj v w → c ≤ C v w)
    (hR : IsRealRobust D ν τ)
    (hIn : ∀ v, α*(Fintype.card V:ℝ) ≤ (inDegree D v:ℝ))
    (hOut : ∀ v, α*(Fintype.card V:ℝ) ≤ (outDegree D v:ℝ))
    (hMinRow : ∀ v, k ≤ ∑ w,M v w) (hMinCol : ∀ w, k ≤ ∑ v,M v w)
    (hRow : ∀ v, let d := (∑ w,M v w)-k
      (1-ε)*ρ*(Fintype.card V:ℝ) ≤ (d:ℝ) ∧ (d:ℝ) ≤ (1+ε)*ρ*(Fintype.card V:ℝ))
    (hCol : ∀ w, let d := (∑ v,M v w)-k
      (1-ε)*ρ*(Fintype.card V:ℝ) ≤ (d:ℝ) ∧ (d:ℝ) ≤ (1+ε)*ρ*(Fintype.card V:ℝ)) :
    ∃ H : V → V → ℕ, (∀ v w, H v w ≤ C v w) ∧
      ∃ F : Fin k → Equiv.Perm V, ∀ v w,
        H v w + ((univ : Finset (Fin k)).filter (fun i => F i v = w)).card = M v w := by
  let p := fun v => (∑ w,M v w)-k
  let q := fun w => (∑ v,M v w)-k
  have hp : (∑ v,p v)+(∑ _ : V,k) = ∑ v,∑ w,M v w := by
    rw [←sum_add_distrib]
    exact sum_congr rfl fun v _ => Nat.sub_add_cancel (hMinRow v)
  have hq : (∑ w,q w)+(∑ _ : V,k) = ∑ w,∑ v,M v w := by
    rw [←sum_add_distrib]
    exact sum_congr rfl fun w _ => Nat.sub_add_cancel (hMinCol w)
  have hBalance : (∑ v,p v) = ∑ w,q w := by
    rw [sum_comm] at hp
    omega
  obtain ⟨H,hH,hHP,hHQ⟩ := osthus_staden_lemma_4_1 C D c ν τ α ε ρ p q
    hν hν1 hντ hτα hε hεν hρ hρν hOrder hCap hR hIn hOut hRow hCol hBalance
  let R := fun v w => M v w-H v w
  have hPay (v w : V) : R v w+H v w = M v w := Nat.sub_add_cancel ((hH v w).trans (hSub v w))
  have hRO (v : V) : ∑ w,R v w = k := by
    have h := sum_congr (s₁ := (univ : Finset V)) rfl (fun w _ => hPay v w)
    rw [sum_add_distrib,hHP] at h
    have hBack : p v+k = univ.sum (M v) := Nat.sub_add_cancel (hMinRow v)
    omega
  have hRI (w : V) : ∑ v,R v w = k := by
    have h := sum_congr (s₁ := (univ : Finset V)) rfl (fun v _ => hPay v w)
    rw [sum_add_distrib,hHQ] at h
    have hMin := hMinCol w
    dsimp only [q] at h
    omega
  obtain ⟨F,hF⟩ := exists_factorization R k hRO hRI
  exact ⟨H,hH,F,fun v w => by rw [hF,add_comm,hPay]⟩

end OverfullWork.DirectedMultigraphFactors
