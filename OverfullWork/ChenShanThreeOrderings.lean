module

public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open Finset
open scoped Classical

private theorem pair_event_lift_le
    {Ω P Q R : Type*} [Fintype Ω] [Fintype P] [Fintype Q] [Fintype R]
    (e : Ω ≃ (P × Q) × R) (bad : P → Q → Prop) (budget : ℝ)
    (h : (((univ : Finset (P × Q)).filter (fun x => bad x.1 x.2)).card : ℝ) ≤
      budget*((Fintype.card P : ℝ)*Fintype.card Q)) :
    (((univ : Finset Ω).filter (fun x => bad (e x).1.1 (e x).1.2)).card : ℝ) ≤
      budget*Fintype.card Ω := by
  let U := (univ : Finset Ω).filter (fun x => bad (e x).1.1 (e x).1.2)
  let T := (univ : Finset (P × Q)).filter (fun x => bad x.1 x.2)
  have hEq : U.map e.toEmbedding = T ×ˢ (univ : Finset R) := by
    ext z
    simp only [mem_product,mem_univ,and_true,mem_map,U,T,mem_filter,true_and]
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact hx
    · intro hz
      exact ⟨e.symm z,by simpa only [e.apply_symm_apply] using hz,e.apply_symm_apply z⟩
  have hCount := congrArg Finset.card hEq
  rw [card_map,card_product,card_univ] at hCount
  change (U.card : ℝ) ≤ _
  rw [hCount,Nat.cast_mul,Fintype.card_congr e]
  simp only [Fintype.card_prod,Nat.cast_mul]
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right h (Nat.cast_nonneg _)

variable {A B W : Type*} [Fintype A] [Fintype B] [Fintype W]

/-- A union bound over all six ordered pairs of independently
permuted classes. Each pair contributes at most its common budget. -/
theorem exists_three_orderings_of_pair_bounds
    (badAB : Equiv.Perm A → Equiv.Perm B → Prop)
    (badBA : Equiv.Perm B → Equiv.Perm A → Prop)
    (badAW : Equiv.Perm A → Equiv.Perm W → Prop)
    (badWA : Equiv.Perm W → Equiv.Perm A → Prop)
    (badBW : Equiv.Perm B → Equiv.Perm W → Prop)
    (badWB : Equiv.Perm W → Equiv.Perm B → Prop) (budget : ℝ)
    (hBudget : 6*budget < 1)
    (hAB : (((univ : Finset (Equiv.Perm A × Equiv.Perm B)).filter (fun x => badAB x.1 x.2)).card : ℝ) ≤
      budget*((Fintype.card (Equiv.Perm A) : ℝ)*Fintype.card (Equiv.Perm B)))
    (hBA : (((univ : Finset (Equiv.Perm B × Equiv.Perm A)).filter (fun x => badBA x.1 x.2)).card : ℝ) ≤
      budget*((Fintype.card (Equiv.Perm B) : ℝ)*Fintype.card (Equiv.Perm A)))
    (hAW : (((univ : Finset (Equiv.Perm A × Equiv.Perm W)).filter (fun x => badAW x.1 x.2)).card : ℝ) ≤
      budget*((Fintype.card (Equiv.Perm A) : ℝ)*Fintype.card (Equiv.Perm W)))
    (hWA : (((univ : Finset (Equiv.Perm W × Equiv.Perm A)).filter (fun x => badWA x.1 x.2)).card : ℝ) ≤
      budget*((Fintype.card (Equiv.Perm W) : ℝ)*Fintype.card (Equiv.Perm A)))
    (hBW : (((univ : Finset (Equiv.Perm B × Equiv.Perm W)).filter (fun x => badBW x.1 x.2)).card : ℝ) ≤
      budget*((Fintype.card (Equiv.Perm B) : ℝ)*Fintype.card (Equiv.Perm W)))
    (hWB : (((univ : Finset (Equiv.Perm W × Equiv.Perm B)).filter (fun x => badWB x.1 x.2)).card : ℝ) ≤
      budget*((Fintype.card (Equiv.Perm W) : ℝ)*Fintype.card (Equiv.Perm B))) :
    ∃ (π : Equiv.Perm A) (σ : Equiv.Perm B) (τ : Equiv.Perm W),
      ¬badAB π σ ∧ ¬badBA σ π ∧ ¬badAW π τ ∧
        ¬badWA τ π ∧ ¬badBW σ τ ∧ ¬badWB τ σ := by
  let P := Equiv.Perm A
  let Q := Equiv.Perm B
  let R := Equiv.Perm W
  let Ω := P × Q × R
  let ab := (Equiv.prodAssoc P Q R).symm
  let ba := ab.trans ((Equiv.prodComm P Q).prodCongr (Equiv.refl R))
  let aw := ((Equiv.refl P).prodCongr (Equiv.prodComm Q R)).trans (Equiv.prodAssoc P R Q).symm
  let wa := aw.trans ((Equiv.prodComm P R).prodCongr (Equiv.refl Q))
  let bw := Equiv.prodComm P (Q × R)
  let wb := bw.trans ((Equiv.prodComm Q R).prodCongr (Equiv.refl P))
  let events : Fin 6 → Ω → Prop :=
    ![fun x => badAB x.1 x.2.1, fun x => badBA x.2.1 x.1,
      fun x => badAW x.1 x.2.2, fun x => badWA x.2.2 x.1,
      fun x => badBW x.2.1 x.2.2, fun x => badWB x.2.2 x.2.1]
  let F (i : Fin 6) := (univ : Finset Ω).filter (events i)
  let U := (univ : Finset (Fin 6)).biUnion F
  have hEach (i : Fin 6) : ((F i).card : ℝ) ≤ budget*Fintype.card Ω := by
    fin_cases i
    · exact pair_event_lift_le ab badAB budget hAB
    · exact pair_event_lift_le ba badBA budget hBA
    · exact pair_event_lift_le aw badAW budget hAW
    · exact pair_event_lift_le wa badWA budget hWA
    · exact pair_event_lift_le bw badBW budget hBW
    · exact pair_event_lift_le wb badWB budget hWB
  have hN : (0 : ℝ) < Fintype.card Ω := by
    exact_mod_cast (Fintype.card_pos_iff.mpr
      ⟨(Equiv.refl A,Equiv.refl B,Equiv.refl W)⟩ : 0 < Fintype.card Ω)
  have hCard : (U.card : ℝ) < Fintype.card Ω := by
    calc
      _ ≤ ∑ i : Fin 6, ((F i).card : ℝ) := by
        exact_mod_cast (card_biUnion_le (s := (univ : Finset (Fin 6))) (t := F))
      _ ≤ ∑ _i : Fin 6, budget*Fintype.card Ω := sum_le_sum fun i _ => hEach i
      _ = (6*budget)*Fintype.card Ω := by
        simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat,mul_assoc]
      _ < _ := by simpa only [one_mul] using mul_lt_mul_of_pos_right hBudget hN
  have hlt : U.card < (univ : Finset Ω).card := by
    rw [card_univ]
    exact_mod_cast hCard
  obtain ⟨x,_,hx⟩ := exists_mem_notMem_of_card_lt_card hlt
  have hAvoid (i : Fin 6) : ¬events i x :=
    fun h => hx (mem_biUnion.mpr ⟨i,mem_univ _,mem_filter.mpr ⟨mem_univ _,h⟩⟩)
  exact ⟨x.1,x.2.1,x.2.2,hAvoid 0,hAvoid 1,hAvoid 2,hAvoid 3,hAvoid 4,hAvoid 5⟩

end OverfullWork.ChenShan
